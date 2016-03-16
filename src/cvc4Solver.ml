open Solver

module CVC4Exec : (Exec with type instance = RealInstance.instance) =
struct
  open RealInstance

  type instance = RealInstance.instance

  let ptrn_success = Str.regexp "^unsat"
  let ptrn_failure = Str.regexp "^sat"
  let ptrn_unknown = Str.regexp "^unknown"
  let ptrn_split = Str.regexp " "

  let ptrn_def = Str.regexp "(define-fun \\(\\w+\\) () Real[ \n\r\t]+(?\\(-? [0-9]*.[0-9]*\\))?)"

  let extract_model debug inst =
    let rec extract_model start result =
      debug (fun _ -> Pp.(str "extract model: " ++ fnl () ++
                          str (String.sub result start (String.length result - start)) ++ fnl ())) ;
      try
        let _ = Str.search_forward ptrn_def result start in
        let var = RealInstance.get_variable (Str.matched_group 1 result) inst in
        let value = Str.matched_group 2 result in
        (var, value) :: extract_model (Str.match_end ()) result
      with
        Not_found -> []
    in extract_model

  let filter_map f =
    let rec filter_map = function
        [] -> []
      | x :: xs ->
        match f x with
          None -> filter_map xs
        | Some x -> x :: filter_map xs
    in filter_map

  let parse_result debug inst result =
    let _ =
      debug (fun _ -> Pp.(str "CVC4 output" ++ fnl () ++ str result))
    in
    let result = Str.global_replace (Str.regexp (Str.quote "\n")) " " result in
    let result = Str.global_replace (Str.regexp (Str.quote "\r")) "" result in
    if Str.string_partial_match ptrn_success result 0 then
      Unsat None
    else if Str.string_match ptrn_failure result 0 then
      Sat []
    else if Str.string_match ptrn_unknown result 0 then
      Unknown
    else
      let _ = Format.eprintf "Bad CVC4 output:\n%s" result in
      assert false

  let execute ~debug inst =
    let (in_channel,out_channel) = Unix.open_process "cvc4 --lang smt -" in
    let _ =
      begin
	let fmt = Format.formatter_of_out_channel out_channel in
	Format.fprintf fmt "(set-option :produce-models true)\n" ;
	Format.fprintf fmt "(set-logic AUFLIRA)\n" ;
        RealInstance.write_instance fmt inst ;
	Format.fprintf fmt "(check-sat)" ;
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
    parse_result debug inst result

end

module CVC4RealSolver = Solver.Make (Solver.RealInstance) (CVC4Exec) ;;

Tactic.SmtTactic.register_smt_solver "cvc4" (fun _ -> CVC4RealSolver.solve)
