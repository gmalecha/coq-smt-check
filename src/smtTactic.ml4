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

module SmtTactic
: sig
    val smtTactic : string option -> unit Proofview.tactic
    val register_smt_solver : string -> (bool -> unit Proofview.tactic) -> unit
  end =
struct

  let contrib_name = "smt-check"

  module Smap =
    Map.Make
      (struct
        type t = string
        let compare = String.compare
      end)

  let all_solvers = ref Smap.empty

  let register_smt_solver name solver =
    all_solvers := Smap.add name solver !all_solvers

  type SmtSolver =
  { name : string
  ; run : bool -> unit Proofview.tactic }

  let pr_SmtSolver s = Pp.(str s.name)

  let smt_parser s =
    if s = "z3" then
      SmtLib2 s
    else if Str.string_match (Str.regexp "smtlib2: (.+)") s 0 then
      SmtLib2 (Str.matched_group 1 s)
    else raise (Failure "invalid solver")

  let the_solver    = ref
  let smt_reader () = Pp.string_of_ppcmds (pr_SmtSolver "z3")
  let smt_setter s  = the_solver := smt_parser s

  let _ =
    declare_string_option
      { opt_sync = false
      ; optdepr  = false
      ; optkey   = ["SMT"; "Solver"]
      ; optname  = "set the smt solver for the smt-check plugin to use"
      ; optread  = smt_reader
      ; optwrite = smt_setter }

  let _ =
    declare_bool_option
      { opt_sync = false
      ; optdepr  = false
      ; optkey   = ["SMT"; "Debug"]
      ; optname  = "print debugging output"
      ; optread  = smt_reader
      ; optwrite = smt_setter }


  (** This is the entry-point to the tactic **)
  let smtTactic = function
      None -> !the_solver !smt_debug
    | Some solver ->
      try
        Smap.find solver !all_solvers !smt_debug
      with
        Not_found ->
        let msg = Pp.(str "No SMT solver named: " ++ qstring solver) in
        Tacticals.New.tclFAIL 1 msg

end

TACTIC EXTEND smt_tac_solve
  | ["smt" "solve"]     ->     [SmtTactic.smtTactic None]
END;;

TACTIC EXTEND smt_tac_solve_with
  | ["smt" "solve" "calling" string(s)] -> [SmtTactic.smtTactic (Some s)]
END;;

TACTIC EXTEND smg_tac_solve_dbg
  | ["smt" "solve_dbg"] ->     [SmtTactic.with_debugging SmtTactic.smtTactic None]
END;;
