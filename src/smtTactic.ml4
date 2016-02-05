open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Errors
open Plugin_utils

DECLARE PLUGIN "smtTactic"

module type Z3Tactic =
sig
  val z3Tactic : unit Proofview.tactic
  val with_debugging : unit Proofview.tactic -> unit Proofview.tactic
end

module Z3Tactic : Z3Tactic =
struct

  let contrib_name = "smt-check"

  module Std = Coqstd.Std
      (struct
        let contrib_name = contrib_name
      end)

  let debug = ref false

  let with_debugging f =
    Proofview.Goal.enter begin fun gl ->
      let copy = !debug in
      let _ = debug := true in
      try
        Proofview.tclBIND f
          (fun x ->
             let _ = debug := copy in
             Proofview.tclUNIT x)
      with
        f ->
	let _ = debug := copy in
	raise f
    end

  let debug f = if !debug then Pp.msg_debug (f ()) else ()

  let r_pkg = ["Coq";"Reals";"Rdefinitions"]
  let logic_pkg = ["Coq";"Init";"Logic"]

  let c_R = Std.resolve_symbol r_pkg "R"
  let c_0 = Std.resolve_symbol r_pkg "R0"
  let c_1 = Std.resolve_symbol r_pkg "R1"
  let c_Rplus = Std.resolve_symbol r_pkg "Rplus"
  let c_Rminus = Std.resolve_symbol r_pkg "Rminus"
  let c_Rdiv = Std.resolve_symbol r_pkg "Rdiv"
  let c_Rmult = Std.resolve_symbol r_pkg "Rmult"
  let c_Ropp = Std.resolve_symbol r_pkg "Ropp"
  let c_Rinv = Std.resolve_symbol r_pkg "Rinv"

  let c_Rlt = Std.resolve_symbol r_pkg "Rlt"
  let c_Rle = Std.resolve_symbol r_pkg "Rle"
  let c_Rgt = Std.resolve_symbol r_pkg "Rgt"
  let c_Rge = Std.resolve_symbol r_pkg "Rge"

  let c_and = Std.resolve_symbol logic_pkg "and"
  let c_or = Std.resolve_symbol logic_pkg "or"
  let c_True = Std.resolve_symbol logic_pkg "True"
  let c_False = Std.resolve_symbol logic_pkg "False"
  let c_Not = Std.resolve_symbol logic_pkg "not"
  let c_eq = Std.resolve_symbol logic_pkg "eq"
  let c_Prop = Term.mkProp

  module ConstrOrd =
  struct
    type t = Term.constr
    let compare = Term.constr_ord
  end


  module Cmap = Map.Make (ConstrOrd)

  type r_type = Prop | R

  type r_expr =
      RConst of float
    | Rplus of r_expr * r_expr
    | Rminus of r_expr * r_expr
    | Rmult of r_expr * r_expr
    | Rdiv of r_expr * r_expr
    | Ropp of r_expr
    | Rinv of r_expr
    | Ropaque of int

  type r_prop =
    | Rtrue
    | Rfalse
    | Rlt of r_expr * r_expr
    | Rle of r_expr * r_expr
    | Rgt of r_expr * r_expr
    | Rge of r_expr * r_expr
    | Req of r_expr * r_expr
    | Rand of r_prop * r_prop
    | Ror of r_prop * r_prop
    | Rimpl of r_prop * r_prop
    | Rnot of r_prop
    | Popaque of int

  let rec print_r_expr out e =
    match e with
      RConst f -> Format.fprintf out "%f" f
    | Rplus (l,r) -> Format.fprintf out "(+ %a %a)" print_r_expr l print_r_expr r
    | Rminus (l,r) -> Format.fprintf out "(- %a %a)" print_r_expr l print_r_expr r
    | Rmult (l,r) -> Format.fprintf out "(* %a %a)" print_r_expr l print_r_expr r
    | Rdiv (l,r) -> Format.fprintf out "(/ %a %a)" print_r_expr l print_r_expr r
    | Ropp l -> Format.fprintf out "(- 0 %a)" print_r_expr l
    | Rinv l -> Format.fprintf out "(/ 1 %a)" print_r_expr l
    | Ropaque l -> Format.fprintf out "x%d" l

  let rec print_r_prop out e =
    match e with
      Rtrue -> Format.fprintf out "true"
    | Rfalse -> Format.fprintf out "false"
    | Rnot l -> Format.fprintf out "(not %a)" print_r_prop l
    | Popaque x -> Format.fprintf out "x%d" x
    | Rand (l,r) -> Format.fprintf out "(and %a %a)" print_r_prop l print_r_prop r
    | Ror (l,r) -> Format.fprintf out "(or %a %a)" print_r_prop l print_r_prop r
    | Rimpl (l,r) -> Format.fprintf out "(=> %a %a)" print_r_prop l print_r_prop r
    | Rle (l,r) -> Format.fprintf out "(<= %a %a)" print_r_expr l print_r_expr r
    | Rlt (l,r) -> Format.fprintf out "(< %a %a)" print_r_expr l print_r_expr r
    | Rge (l,r) -> Format.fprintf out "(>= %a %a)" print_r_expr l print_r_expr r
    | Rgt (l,r) -> Format.fprintf out "(> %a %a)" print_r_expr l print_r_expr r
    | Req (l,r) -> Format.fprintf out "(= %a %a)" print_r_expr l print_r_expr r

  let conclusion_name = "__CONCLUSION__"

  let print_identifier out id =
    Format.fprintf out "%s" (Names.string_of_id id)

  let print_r_assert out (nm,e) =
    Format.fprintf out "(assert (! %a :named %a))" print_r_prop e print_identifier nm

  let print_type out t =
    match t with
      Prop -> Format.fprintf out "Bool"
    | R -> Format.fprintf out "Real"

  let pr_list sep pr =
    let rec pr_list out ls =
      match ls with
	[] -> ()
      | [l] -> Format.fprintf out "%a" pr l
      | l :: ls -> Format.fprintf out "%a%s%a" pr l sep pr_list ls
    in
    pr_list

  let pr_decls out =
    Cmap.iter (fun _ (k,v) -> Format.fprintf out "(declare-const x%d %a)" k print_type v)

  let pr_smt2 (sep : string) out (tbl, stmts) =
    Format.fprintf out "%a%a"
		   pr_decls tbl
		   (pr_list sep print_r_assert) stmts

  let ptrn_success = Str.regexp "^unsat (\\([^)]*\\))"
  let ptrn_failure = Str.regexp "^sat ([^)]*) (model\\(.+\\)) ?$"
  let ptrn_unknown = Str.regexp "^unknown"
  let ptrn_split = Str.regexp " "

  let ptrn_def = Str.regexp "(define-fun x\\([0-9]+\\) () Real[ \n\r\t]+(?\\(-? [0-9]*.[0-9]*\\))?)"

  type z3_result =
      Sat of (int * float) list
    | Unsat of Names.identifier list
    | Unknown


  let rec extract_model start result =
    debug (fun _ -> Pp.(str "extract model: " ++ fnl () ++
                        str (String.sub result start (String.length result - start)) ++ fnl ())) ;
    try
      let _ = Str.search_forward ptrn_def result start in
      let num = int_of_string (Str.matched_group 1 result) in
      let value = Str.matched_group 2 result in
      let value =
	try
	  let _ = String.index value '-' in
	  "-" ^ String.sub value 2 (String.length value - 2)
	with
	  Not_found -> value
      in
      let value = float_of_string value in
      (num, value) :: extract_model (Str.match_end ()) result
    with
      Not_found -> []

  let parse_Z3_result result =
    let _ =
      debug (fun _ -> Pp.(str "Z3 output" ++ fnl () ++ str result))
    in
    let result = Str.global_replace (Str.regexp (Str.quote "\n")) " " result in
    let result = Str.global_replace (Str.regexp (Str.quote "\r")) "" result in
    if Str.string_partial_match ptrn_success result 0 then
      let lst = Str.matched_group 1 result in
      Unsat (List.map Names.id_of_string (Str.split ptrn_split lst))
    else if Str.string_match ptrn_failure result 0 then
      let result = Str.matched_group 1 result in
      Sat (extract_model 0 result)
    else if Str.string_match ptrn_unknown result 0 then
      Unknown
    else
      let _ = Format.eprintf "Bad Z3 output:\n%s" result in
      assert false

  let runZ3 tbl stmts =
    let (in_channel,out_channel) = Unix.open_process "z3 -in -smt2" in
    let _ =
      begin
	let fmt = Format.formatter_of_out_channel out_channel in
	Format.fprintf fmt "(set-option :produce-unsat-cores true)\n" ;
	Format.fprintf fmt "(set-option :produce-models true)\n" ;
	Format.fprintf fmt "%a" (pr_smt2 "") (tbl, stmts) ;
	Format.fprintf fmt "(check-sat)\n(get-unsat-core)\n(get-model)" ;
	Format.pp_print_flush fmt () ;
	flush out_channel ;
	close_out out_channel
      end
    in
    let buffer_size = 2048 in
    let buffer = Buffer.create buffer_size in
    let string = String.create buffer_size in
    let chars_read = ref 1 in
    while !chars_read <> 0 do
      chars_read := input in_channel string 0 buffer_size;
      Buffer.add_substring buffer string 0 !chars_read
    done;
    ignore (Unix.close_process (in_channel, out_channel));
    let result = Buffer.contents buffer in
    parse_Z3_result result

  let parse_uop recur constr op =
    (Term_match.apps (Term_match.Glob constr)
		     [Term_match.get 0],
     fun tbl bindings ->
     let (res,tbl) = recur tbl (Hashtbl.find bindings 0) in
     (op res, tbl))

  let parse_bop recur constr op =
    (Term_match.apps (Term_match.Glob constr)
		     [Term_match.get 0;Term_match.get 1],
     fun tbl bindings ->
     let (l,tbl) = recur tbl (Hashtbl.find bindings 0) in
     let (r,tbl) = recur tbl (Hashtbl.find bindings 1) in
     (op l r, tbl))

  let rec parse_expr tbl =
    Term_match.matches tbl
      [ (Term_match.Glob c_0, fun tbl _ -> (RConst 0., tbl))
      ; (Term_match.Glob c_1, fun tbl _ -> (RConst 1., tbl))
      ; parse_bop parse_expr c_Rplus (fun a b -> Rplus (a,b))
      ; parse_bop parse_expr c_Rminus (fun a b -> Rminus (a,b))
      ; parse_bop parse_expr c_Rmult (fun a b -> Rmult (a,b))
      ; parse_bop parse_expr c_Rdiv (fun a b -> Rdiv (a,b))
      ; parse_uop parse_expr c_Ropp (fun a -> Ropp a)
      ; parse_uop parse_expr c_Rinv (fun a -> Rinv a)
      ; (Term_match.get 0,
	 fun tbl binders ->
	 let trm = Hashtbl.find binders 0 in
	 try
	   (Ropaque (fst (Cmap.find trm tbl)), tbl)
	 with
	   Not_found ->
	   let nxt = Cmap.cardinal tbl in
	   (Ropaque nxt, Cmap.add trm (nxt,R) tbl))
      ]

  let rec parse_prop tbl =
    Term_match.matches tbl
      [ parse_bop parse_expr c_Rlt (fun a b -> Rlt (a,b))
      ; parse_bop parse_expr c_Rle (fun a b -> Rle (a,b))
      ; parse_bop parse_expr c_Rgt (fun a b -> Rgt (a,b))
      ; parse_bop parse_expr c_Rge (fun a b -> Rge (a,b))
      ; (Term_match.apps (Term_match.Glob c_eq)
			 [Term_match.Glob c_R;
			  Term_match.get 0;
			  Term_match.get 1],
	 fun tbl bindings ->
	 let (l,tbl) = parse_expr tbl (Hashtbl.find bindings 0) in
	 let (r,tbl) = parse_expr tbl (Hashtbl.find bindings 1) in
	 (Req (l, r), tbl))
      ; parse_bop parse_prop c_and (fun a b -> Rand (a,b))
      ; parse_bop parse_prop c_or  (fun a b -> Ror (a,b))
      ; (Term_match.apps (Term_match.Glob c_Not)
	   [Term_match.get 0], fun tbl bindings ->
	     let (l,tbl) = parse_prop tbl (Hashtbl.find bindings 0) in
	     (Rnot l, tbl))
      ; (Term_match.Glob c_True, fun tbl _ -> (Rtrue, tbl))
      ; (Term_match.Glob c_False, fun tbl _ -> (Rfalse, tbl))
      ; (Term_match.get 0,
	 fun tbl binders ->
	 let trm = Hashtbl.find binders 0 in
	 try
	   (Popaque (fst (Cmap.find trm tbl)), tbl)
	 with
	   Not_found ->
	   begin
	     let nxt = Cmap.cardinal tbl in
	     (Popaque nxt, Cmap.add trm (nxt,Prop) tbl)
	   end)
      ]

  let pp_list (pp : 'a -> Pp.std_ppcmds) (pp_sep : unit -> Pp.std_ppcmds) =
    let rec pp_list (ls : 'a list) : Pp.std_ppcmds =
      match ls with
	[] -> Pp.spc ()
      | [x] -> pp x
      | x :: xs -> Pp.(++) (pp x)  (Pp.(++) (pp_sep ()) (pp_list xs))
    in
    pp_list

  let pr_unsat_core ls =
    pp_list Ppconstr.pr_id Pp.spc ls

  let pr_model tbl =
    let rec find x =
      match Cmap.fold (fun k (v,_) acc -> if v = x then Some k else acc) tbl None with
	None -> assert false
      | Some x -> x
    in
    let pp_assign (x,v) =
      let vv : float = v in
      Pp.(   Printer.pr_constr (find x)
	  ++ str " = " ++ real vv)
    in
    begin
    fun x ->
      match x with
      | [] -> assert false
      | _ ->
	pp_list pp_assign Pp.fnl x
    end

  let maybe_parse check tbl (name, decl, trm) =
    if check trm then
      try
	let (p,tbl) = parse_prop tbl trm in
	Some (tbl, (name, p))
      with
	Term_match.Match_failure -> None
    else
      None

  let z3Tactic =
    Proofview.Goal.nf_enter begin fun gl ->
    let goal = Proofview.Goal.concl gl in
    let hyps = Proofview.Goal.hyps gl in

    let is_prop p =
      let (_,ty) = Typing.type_of (Proofview.Goal.env gl)
          (Proofview.Goal.sigma gl) p in
      Term.eq_constr ty Term.mkProp
    in

    let tbl = Cmap.empty in
    match maybe_parse (fun _ -> true) tbl
		      (Names.id_of_string conclusion_name, None, goal)
    with
      None ->
      Tacticals.New.tclFAIL 0 (Pp.str "z3 plugin failed to parse goal")
    | Some (tbl, (name, concl)) ->
       let acc = (tbl, [(name, Rnot concl)]) in
       let (tbl,hyps) =
	 List.fold_left (fun (tbl,acc) t ->
			 match maybe_parse is_prop tbl t with
			   None -> (tbl, acc)
			 | Some (tbl, hyp) -> (tbl, hyp::acc)) acc hyps
       in
       let _ =
	 debug (fun _ ->
		let _ = Format.fprintf Format.str_formatter "%a" (pr_smt2 "\n") (tbl,hyps) in
		let msg = Format.flush_str_formatter () in
		let _ = Format.eprintf "%a" (pr_smt2 "\n") (tbl, hyps) in
		Pp.str msg)
       in
       match runZ3 tbl hyps with
         Sat model ->
	 let msg =
	   Pp.(   str "z3 failed to solve the goal."
               ++ fnl ()
	       ++ pr_model tbl model)
	 in
	 Tacticals.New.tclFAIL 0 msg
       | Unsat core ->
	  let msg =
	    Pp.(   str "z3 solved the goal using only"
                ++ spc ()
                ++ pr_unsat_core core)
	  in
          Proofview.V82.tactic (Tacticals.tclIDTAC_MESSAGE msg)
       | Unknown ->
         let msg =
           Pp.(str "z3 returned unknown")
         in
         Tacticals.New.tclFAIL 0 msg
    end
end

TACTIC EXTEND z3_tac
  | ["z3" "solve"]     ->     [Z3Tactic.z3Tactic]
END;;

TACTIC EXTEND z3_tac_dbg
  | ["z3" "solve_dbg"] ->     [Z3Tactic.with_debugging Z3Tactic.z3Tactic]
END;;
