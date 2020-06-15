module type Solver =
sig
  val solve : debug:bool -> verbose:bool -> unit Proofview.tactic
end


module type Instance =
sig
  type instance

  val parse_conclusion : Environ.env -> Evd.evar_map ->
    EConstr.t -> instance

  val parse_hypothesis : Environ.env -> Evd.evar_map ->
    Names.Id.t -> EConstr.t -> instance -> instance

  val write_instance : ?pretty:bool -> Format.formatter -> instance -> unit

  val get_variable : string -> instance -> EConstr.t

  (* Returning [None] means the conclusion *)
  val get_hypothesis : string -> instance -> Names.Id.t option
end

module ParseOnlyProp (I : Instance) : Instance with type instance = I.instance

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
    (Parse : Instance)
    (Exec : Exec with type instance = Parse.instance) : Solver

module RealInstance : Instance
