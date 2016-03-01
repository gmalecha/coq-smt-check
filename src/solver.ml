open Plugin_utils

module type Solver =
sig
  val solve : bool -> unit Proofview.tactic
end

module type Instance =
sig
  type instance

  val parse_conclusion : Environ.env -> Evd.evar_map ->
    Term.constr -> instance

  val parse_hypothesis : Environ.env -> Evd.evar_map ->
    Names.Id.t -> Term.constr -> instance -> instance

  val write_instance : ?pretty:bool -> Format.formatter -> instance -> unit

  val get_variable : string -> instance -> Term.constr

  (* Returning [None] means the conclusion *)
  val get_hypothesis : string -> instance -> Names.identifier option
end

module ParseOnlyProp (P : Instance) :
  (Instance with type instance = P.instance) =
struct
  type instance = P.instance

  let is_a_prop env evm t =
    let (_,ty) = Typing.type_of env evm t in
    Term.eq_constr ty Term.mkProp

  let parse_conclusion env evm c =
    if is_a_prop env evm c then
      P.parse_conclusion env evm c
    else
      raise (Failure "Conclusion is not a proposition")

  let parse_hypothesis env evm name typ i =
    if is_a_prop env evm typ then
      P.parse_hypothesis env evm name typ i
    else i

  let write_instance = P.write_instance
  let get_variable = P.get_variable
  let get_hypothesis = P.get_hypothesis
end

type smt_result =
    Sat of (Term.constr * string) list
  | Unsat of (bool * Names.identifier list) option (* the core *)
  | Unknown

module type Exec =
sig
  type instance

  val execute : instance -> smt_result
end

module Make
    (Inst : Instance)
    (Exec : Exec with type instance = Inst.instance) : Solver =
struct
  open Inst
  open Exec

  let parse_instance env evm hyps concl =
    let res = Inst.parse_conclusion env evm concl in
    List.fold_left (fun acc (name, _decl, typ) ->
        Inst.parse_hypothesis env evm name typ acc) res hyps

  module Std = Coqstd.Std
      (struct
        let contrib_name = "smt-check-real-instance"
      end)

  let false_type : Term.constr Lazy.t =
    Std.resolve_symbol ["Coq";"Init";"Logic"] "False"

  let pr_model env evm =
    Pp.pr_vertical_list
      (fun (var,value) ->
         Pp.(Printer.pr_constr_env env evm var ++
             spc () ++ str "=" ++ spc () ++ str value))

  let solve verbose =
    Proofview.Goal.nf_enter begin fun gl ->
    let goal = Proofview.Goal.concl gl in
    let hyps = Proofview.Goal.hyps gl in
    let env  = Proofview.Goal.env gl in
    let evm  = Proofview.Goal.sigma gl in

    try
      let inst = parse_instance env evm hyps goal in
      match Exec.execute inst with
        Sat model when verbose ->
        let msg =
	   Pp.(   str "z3 failed to solve the goal."
               ++ fnl ()
	       ++ pr_model env evm model)
	in
        Tacticals.New.tclFAIL 0 msg
      | Sat _ ->
        Tacticals.New.tclFAIL 0 Pp.(str "Satisfiable")
      | Unsat (Some (need_concl, core)) ->
        let open Proofview.Monad in
        (if not need_concl
         then Tactics.elim_type (Lazy.force false_type)
         else Proofview.tclUNIT ()) >>
        (Tactics.keep core)
      | Unsat None ->
        Tacticals.New.tclIDTAC
      | Unknown ->
        Tacticals.New.tclFAIL 0 Pp.(str "solver returned unkown")
    with
      Failure msg ->
      Tacticals.New.tclFAIL 0 Pp.(str "failed to parse the goal")
    end

end


module RealInstance : Instance =
struct

  module Std = Coqstd.Std
      (struct
        let contrib_name = "smt-check-real-instance"
      end)

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

  type instance =
    { vars : (int * r_type) Cmap.t
    ; assertions : (Names.identifier * r_prop) list
    ; concl : r_prop }

  let get_opaque x t i =
    try fst (Cmap.find x i), i
    with
      Not_found ->
      let nxt = Cmap.cardinal i in
      nxt, (Cmap.add x (nxt, t) i)


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
           let (o,tbl) = get_opaque trm Prop tbl in
	   (Popaque o, tbl))
      ]

  let parse_hypothesis _ _ name typ i =
    let (h,vs) = parse_prop i.vars typ in
    { i with vars = vs ; assertions = (name, h) :: i.assertions }

  let parse_conclusion _ _ x =
    let (c,vs) = parse_prop Cmap.empty x in
    { vars = vs ; assertions = [] ; concl = c }

  (** Printing **)
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


  let print_identifier out id =
    Format.fprintf out "%s" (Names.string_of_id id)

  let print_named_assert pr_id out (nm,e) =
    Format.fprintf out "(assert (! %a :named %a))" print_r_prop e pr_id nm

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
    Cmap.iter (fun _ (k,v) ->
        Format.fprintf out "(declare-const x%d %a)" k print_type v)

  let print_a_string out s =
    Format.fprintf out "%s" s

  let conclusion_name = "__CONCLUSION__"

  let write_instance ?pretty:(pretty=false) out inst =
    let sep = if pretty then "\n" else "" in
    Format.fprintf out "%a%a%s%a"
      pr_decls inst.vars
      (pr_list sep (print_named_assert print_identifier)) inst.assertions
      sep
      (print_named_assert print_a_string) (conclusion_name, Rnot inst.concl)

  let get_variable x inst =
    assert (String.length x > 1) ;
    let x =
      let rest = String.sub x 1 (String.length x - 1) in
      int_of_string rest
    in
    match
      Cmap.fold (fun k (var, _) acc ->
          if var = x then Some k else acc)
        inst.vars None
    with
      None -> raise Not_found
    | Some x -> x

  let get_hypothesis x inst =
    if x = conclusion_name then None
    else Some (Names.id_of_string x)

end
