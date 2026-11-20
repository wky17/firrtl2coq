let () =
 if Array.length Sys.argv <> 3 then (prerr_endline "Usage: main_lo INPUT OUTPUT"; exit 2);
 let ast = try Hifirrtl_lang.Parser.hiparse Sys.argv.(1) with e -> prerr_endline ("PARSE: "^Printexc.to_string e); exit 3 in
 try let oc=open_out Sys.argv.(2) in Coqgen_lo.emit_file oc ast; close_out oc
 with e -> prerr_endline ("CONVERT: "^Printexc.to_string e); exit 4
