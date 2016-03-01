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

module ParseOnlyProp (I : Instance) : Instance with type instance = I.instance

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
    (Parse : Instance)
    (Exec : Exec with type instance = Parse.instance) : Solver

module RealInstance : Instance
