let () =
  Printexc.record_backtrace true;
  try
    if Array.length Sys.argv < 3 then
      (Printf.eprintf "Usage: hipparser INPUT.fir OUTPUT.v\n"; exit 2);
    let ast = Hifirrtl_lang.Parser.hiparse Sys.argv.(1) in
    let ((modmap, _), maps) = Transhiast_without_inline.mapcir ast in
    let cir = Transhiast_without_inline.trans_cir ast modmap maps in
    let oc = open_out Sys.argv.(2) in
    Coqgen.emit_file oc cir;
    close_out oc
  with
  | Not_found ->
      Printf.eprintf "Fatal conversion error: a requested name was not found.\n%s\n"
        (Printexc.get_backtrace ());
      exit 1
  | Failure msg ->
      Printf.eprintf "Fatal conversion error: %s\n%s\n" msg
        (Printexc.get_backtrace ());
      exit 1
  | exn ->
      Printf.eprintf "Fatal conversion error: %s\n%s\n"
        (Printexc.to_string exn) (Printexc.get_backtrace ());
      exit 1
(*
  if Array.length Sys.argv < 3 then
    (Printf.eprintf "Usage: hipparser INPUT.fir OUTPUT.v\n"; exit 2);
  let ast = Hifirrtl_lang.Parser.hiparse Sys.argv.(1) in
  let ((modmap, _), maps) = Transhiast_without_inline.mapcir ast in
  let cir = Transhiast_without_inline.trans_cir ast modmap maps in
  let oc = open_out Sys.argv.(2) in
  Coqgen.emit_file oc cir;
  close_out oc
*)
