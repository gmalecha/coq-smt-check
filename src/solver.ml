open Names
open Util


module type Solver =
sig
  val solve : debug:bool -> verbose:bool -> unit Proofview.tactic
end

module type Instance =
sig
  type instance

  val parse_conclusion : Environ.env -> Evd.evar_map ->
    Evd.econstr -> instance

  val parse_hypothesis : Environ.env -> Evd.evar_map ->
    Names.Id.t -> Evd.econstr -> instance -> instance

  val write_instance : ?pretty:bool -> Format.formatter -> instance -> unit

  val get_variable : string -> instance -> EConstr.t

  (* Returning [None] means the conclusion *)
  val get_hypothesis : string -> instance -> Names.Id.t option
end

module ParseOnlyProp (P : Instance) :
  (Instance with type instance = P.instance) =
struct
  type instance = P.instance

  let is_a_prop env evm (t : EConstr.t) =
    let (_,ty) = Typing.type_of env evm t in
    EConstr.eq_constr evm ty EConstr.mkProp

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
    Sat of (EConstr.t * string) list
  | Unsat of (bool * Names.Id.t list) option (* the core *)
  | Unknown

module type Exec =
sig
  type instance

  val execute : debug:((unit -> Pp.t) -> unit) -> instance -> smt_result
end

module Make
    (Inst : Instance)
    (Exec : Exec with type instance = Inst.instance) : Solver =
struct
  let parse_instance env evm hyps concl =
    let res = Inst.parse_conclusion env evm concl in
    List.fold_left (fun acc -> function
        | Context.Named.Declaration.LocalAssum (name, typ) ->
          Inst.parse_hypothesis env evm name.Context.binder_name typ acc
        | Context.Named.Declaration.LocalDef (name, _, typ) ->
          Inst.parse_hypothesis env evm name.Context.binder_name typ acc) res hyps

  (* module Std = Coqstd.Std
   *     (struct
   *       let contrib_name = "smt-check-real-instance"
   *     end) *)

  let false_type : EConstr.t Lazy.t =
    lazy (assert false) (* Std.resolve_symbol ["Coq";"Init";"Logic"] "False" *)

  let pr_model env evm =
    Pp.pr_vertical_list
      (fun (var,value) ->
         Pp.(Printer.pr_econstr_env env evm var ++
             spc () ++ str "=" ++ spc () ++ str value))

  let solve ~debug ~verbose =
    let debug =
      if debug then (fun x -> Feedback.msg_debug (x ()))
      else fun _ -> ()
    in
    Proofview.Goal.enter (fun gl ->
        let goal = Proofview.Goal.concl gl in
        let hyps = Proofview.Goal.hyps gl in
        let env  = Proofview.Goal.env gl in
        let evm  = Proofview.Goal.sigma gl in

        try
          let inst = parse_instance env evm hyps goal in
          match Exec.execute ~debug inst with
            Sat model when verbose ->
            let msg =
	      Pp.(   str "solver failed to solve the goal."
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
    )

end

module RealInstance : Instance =
struct
  (* module Std = Coqstd.Std
   *     (struct
   *       let contrib_name = "smt-check-real-instance"
   *     end) *)

  let resolve (tm : string) : GlobRef.t Lazy.t =
    lazy (Coqlib.lib_ref tm)

  let r_real s = resolve ("Coq.Reals.Rdefinitions." ^ s)
  let r_logic s = resolve ("Coq.Init.Logic." ^ s)

  let c_R = r_real "R"
  let c_0 = r_real "R0"
  let c_1 = r_real "R1"
  let c_Rplus = r_real "Rplus"
  let c_Rminus = r_real "Rminus"
  let c_Rdiv = r_real "Rdiv"
  let c_Rmult = r_real "Rmult"
  let c_Ropp = r_real "Ropp"
  let c_Rinv = r_real "Rinv"

  let c_Rlt = r_real "Rlt"
  let c_Rle = r_real "Rle"
  let c_Rgt = r_real "Rgt"
  let c_Rge = r_real "Rge"

  let c_and = r_logic "and"
  let c_or = r_logic "or"
  let c_True = r_logic "True"
  let c_False = r_logic "False"
  let c_Not = r_logic "not"
  let c_eq = r_logic "eq"
  let c_Prop = Constr.mkProp

  module EConstrOrd =
  struct
    type t = EConstr.t
    let compare a b =
      Constr.compare (EConstr.Unsafe.to_constr a) (EConstr.Unsafe.to_constr b)
  end

  (* constr maps *)
  module ECmap = Map.Make(EConstrOrd)

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
    { vars : (int * r_type) ECmap.t
    ; assertions : (Names.Id.t * r_prop) list
    ; concl : r_prop }

  let get_opaque x t i =
    try fst (ECmap.find x i), i
    with
      Not_found ->
      let nxt = ECmap.cardinal i in
      nxt, (ECmap.add x (nxt, t) i)


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

  let rec parse_expr evd tbl =
    Term_match.ematches tbl
      [ (Term_match.Glob c_0, fun tbl _ -> (RConst 0., tbl))
      ; (Term_match.Glob c_1, fun tbl _ -> (RConst 1., tbl))
      ; parse_bop (parse_expr evd) c_Rplus (fun a b -> Rplus (a,b))
      ; parse_bop (parse_expr evd) c_Rminus (fun a b -> Rminus (a,b))
      ; parse_bop (parse_expr evd) c_Rmult (fun a b -> Rmult (a,b))
      ; parse_bop (parse_expr evd) c_Rdiv (fun a b -> Rdiv (a,b))
      ; parse_uop (parse_expr evd) c_Ropp (fun a -> Ropp a)
      ; parse_uop (parse_expr evd) c_Rinv (fun a -> Rinv a)
      ; (Term_match.get 0,
	 fun tbl binders ->
	 let trm = Hashtbl.find binders 0 in
	 try
	   (Ropaque (fst (ECmap.find trm tbl)), tbl)
	 with
	   Not_found ->
	   let nxt = ECmap.cardinal tbl in
	   (Ropaque nxt, ECmap.add trm (nxt,R) tbl))
      ] evd

  let rec parse_prop evd tbl =
    Term_match.ematches tbl
      [ parse_bop (parse_expr evd) c_Rlt (fun a b -> Rlt (a,b))
      ; parse_bop (parse_expr evd) c_Rle (fun a b -> Rle (a,b))
      ; parse_bop (parse_expr evd) c_Rgt (fun a b -> Rgt (a,b))
      ; parse_bop (parse_expr evd) c_Rge (fun a b -> Rge (a,b))
      ; (Term_match.apps (Term_match.Glob c_eq)
			 [Term_match.Glob c_R;
			  Term_match.get 0;
			  Term_match.get 1],
	 fun tbl bindings ->
	 let (l,tbl) = parse_expr evd tbl (Hashtbl.find bindings 0) in
	 let (r,tbl) = parse_expr evd tbl (Hashtbl.find bindings 1) in
	 (Req (l, r), tbl))
      ; parse_bop (parse_prop evd) c_and (fun a b -> Rand (a,b))
      ; parse_bop (parse_prop evd) c_or  (fun a b -> Ror (a,b))
      ; (Term_match.apps (Term_match.Glob c_Not)
	   [Term_match.get 0], fun tbl bindings ->
	     let (l,tbl) = parse_prop evd tbl (Hashtbl.find bindings 0) in
	     (Rnot l, tbl))
      ; (Term_match.Glob c_True, fun tbl _ -> (Rtrue, tbl))
      ; (Term_match.Glob c_False, fun tbl _ -> (Rfalse, tbl))
      ; (Term_match.get 0,
	 fun tbl binders ->
           let trm = Hashtbl.find binders 0 in
           let (o,tbl) = get_opaque trm Prop tbl in
	   (Popaque o, tbl))
      ] evd

  let parse_hypothesis _ evd name typ i =
    let (h,vs) = parse_prop evd i.vars typ in
    { i with vars = vs ; assertions = (name, h) :: i.assertions }

  let parse_conclusion _ evd x =
    let (c,vs) = parse_prop evd ECmap.empty x in
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
    Format.fprintf out "%s" (Names.Id.to_string id)

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
    ECmap.iter (fun _ (k,v) ->
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
      ECmap.fold (fun k (var, _) acc ->
          if var = x then Some k else acc)
        inst.vars None
    with
      None -> raise Not_found
    | Some x -> x

  let get_hypothesis x inst =
    if x = conclusion_name then None
    else Some (Names.Id.of_string x)

end
