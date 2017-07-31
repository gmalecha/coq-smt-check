open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Stdarg (* for `wit_string`, the string argument parser *)
open Plugin_utils

DECLARE PLUGIN "smtTactic"

module SmtTactic
: sig
    val smtTactic : ?debug:bool -> ?verbose:bool -> string option -> unit Proofview.tactic
    val register_smt_solver : string -> (string -> debug:bool -> verbose:bool -> unit Proofview.tactic) -> unit
  end =
struct

  let contrib_name = "smt-check"

  module Scmp =
  struct
    type t = string
    let compare = String.compare
  end
  module Smap = Map.Make (Scmp)

  let smt_debug = ref false

  let all_solvers : (string -> debug:bool -> verbose:bool -> unit Proofview.tactic) Smap.t ref =
    ref Smap.empty

  let register_smt_solver (name : string)
      (solver : string -> debug:bool -> verbose:bool -> unit Proofview.tactic) =
    all_solvers := Smap.add name solver !all_solvers

  type smtSolver =
    { name : string
    ; run : debug:bool -> verbose:bool -> unit Proofview.tactic }

  let the_solver    =
    ref { name = "<unset>"
        ; run = fun ~debug ~verbose ->
            Tacticals.New.tclFAIL 0 Pp.(str "solver not set") }

  let smt_parser s =
    let (name, args) =
      try
        let split = String.index s ':' in
        let first = String.sub s 0 (split - 1) in
        let arg = String.sub s split (String.length s - split) in
        (first, arg)
      with
        Not_found -> (s,"")
    in
    try
      let solver = Smap.find name !all_solvers in
      { name =
          if args = "" then name
          else name ^ ": " ^ args
      ; run = solver args }
    with
      Not_found ->
      raise (Failure ("Unknown solver: " ^ name))

  let smt_reader () = !the_solver.name
  let smt_setter s =
    the_solver := smt_parser s

  let _ =
    Goptions.(declare_string_option
      { optsync  = false
      ; optdepr  = false
      ; optkey   = ["SMT"; "Solver"]
      ; optname  = "set the smt solver for the smt-check plugin to use"
      ; optread  = smt_reader
      ; optwrite = smt_setter })

  let _ =
    Goptions.(declare_bool_option
      { optsync  = false
      ; optdepr  = false
      ; optkey   = ["SMT"; "Debug"]
      ; optname  = "print debugging output"
      ; optread  = (fun () -> !smt_debug)
      ; optwrite = (:=) smt_debug })

  (** This is the entry-point to the tactic **)
  let smtTactic ?debug ?verbose opt =
    let debug = Option.default !smt_debug debug in
    let verbose = Option.default false verbose in
    match opt with
      None -> (!the_solver).run ~debug ~verbose
    | Some solver ->
      try
        (smt_parser solver).run ~debug ~verbose
      with
        Not_found ->
        let msg = Pp.(str "No SMT solver named: " ++ qstring solver) in
        Tacticals.New.tclFAIL 1 msg

end

(** TODO: Clean this up **)

TACTIC EXTEND smt_tac_solve
  | ["smt" "solve"] -> [SmtTactic.smtTactic ~verbose:true None]
END;;

TACTIC EXTEND smt_tac_solve_dbg
  | ["smt" "solve_dbg"] ->
    [SmtTactic.smtTactic ~debug:true ~verbose:true None]
END;;

TACTIC EXTEND smt_tac_solve_dbg_calling
  | ["smt" "solve_dbg" "calling" string(s) ] ->
    [SmtTactic.smtTactic ~debug:true ~verbose:true (Some s)]
END;;

TACTIC EXTEND smt_tac_solve_calling
  | ["smt" "solve" "calling" string(s)] -> [SmtTactic.smtTactic ~verbose:true (Some s)]
END;;
