open Solver

module Z3Exec (I : Instance) : (Exec with type instance = I.instance) =
struct
  type instance = I.instance

  let ptrn_success = Str.regexp "^unsat (\\([^)]*\\))"
  let ptrn_failure = Str.regexp "^sat ([^)]*) (model\\(.+\\)) ?$"
  let ptrn_unknown = Str.regexp "^unknown"
  let ptrn_split = Str.regexp " "

  let ptrn_def =
    Str.regexp "(define-fun \\([^ ]+\\) () Real[ \r\n]+\\([^)]+\\))"

  let extract_model debug inst start result =
    debug (fun _ ->
        Pp.(str "extract model: " ++ fnl () ++
            str (String.sub result start (String.length result - start)) ++ fnl ())) ;
    let rec extract_model start result =
      try
        let _ = Str.search_forward ptrn_def result start in
        let var = I.get_variable (Str.matched_group 1 result) inst in
        let value = Str.matched_group 2 result in
        (var, value) :: extract_model (Str.match_end ()) result
      with
        Not_found -> []
    in extract_model start result

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
      debug (fun _ -> Pp.(str "Z3 output" ++ fnl () ++ str result))
    in
    let result = Str.global_replace (Str.regexp (Str.quote "\n")) " " result in
    let result = Str.global_replace (Str.regexp (Str.quote "\r")) "" result in
    if Str.string_partial_match ptrn_success result 0 then
      let lst = Str.matched_group 1 result in
      let names = Str.split ptrn_split lst in
      let names = List.map (fun x -> I.get_hypothesis x inst) names in
      Unsat (Some (List.exists (function None -> true | _ -> false) names,
                   filter_map (fun x -> x) names))
    else if Str.string_match ptrn_failure result 0 then
      let result = Str.matched_group 1 result in
      Sat (extract_model debug inst 0 result)
    else if Str.string_match ptrn_unknown result 0 then
      Unknown
    else
      let _ = Format.eprintf "Bad Z3 output:\n%s" result in
      assert false

  let execute ~debug inst =
    let (in_channel,out_channel) = Unix.open_process "z3 -in -smt2" in
    let _ =
      begin
	let fmt = Format.formatter_of_out_channel out_channel in
	Format.fprintf fmt "(set-option :produce-unsat-cores true)\n" ;
	Format.fprintf fmt "(set-option :produce-models true)\n" ;
        I.write_instance fmt inst ;
	Format.fprintf fmt "(check-sat)\n(get-unsat-core)\n(get-model)" ;
	Format.pp_print_flush fmt () ;
	flush out_channel ;
	close_out out_channel
      end
    in
    let buffer_size = 2048 in
    let buffer = Buffer.create buffer_size in
    let string = Bytes.create buffer_size in
    let chars_read = ref 1 in
    while !chars_read <> 0 do
      chars_read := input in_channel string 0 buffer_size;
      Buffer.add_subbytes buffer string 0 !chars_read
    done;
    ignore (Unix.close_process (in_channel, out_channel));
    let result = Buffer.contents buffer in
    parse_result debug inst result

end

module Z3RealSolver = Solver.Make (Solver.RealInstance) (Z3Exec) ;;

Tactic.SmtTactic.register_smt_solver "z3" (fun _ -> Z3RealSolver.solve)
