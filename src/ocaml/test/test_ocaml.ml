let numeric_value bits =
  List.fold_right
    (fun b n -> Z.add (if b then Z.one else Z.zero) (Z.shift_left n 1))
    bits Z.zero

let check_literal label width input =
  let bits = Transhiast.bits_of_z input width in
  let expected = if width = 0 then Z.zero else Z.extract input 0 width in
  let actual = numeric_value bits in
  if List.length bits <> width || not (Z.equal actual expected) then
    failwith (Printf.sprintf "%s: width=%d expected=%s actual=%s"
      label width (Z.to_string expected) (Z.to_string actual));
  if width <= 32 && Extraction.NBitsDef.to_N bits <> Z.to_int expected then
    failwith (label ^ ": disagrees with the extracted Coq NBits decoder")

let () =
  List.iter (fun (label,width,value) -> check_literal label width (Z.of_string value))
    ["NOP",32,"0x13"; "instruction mask",32,"0x707f";
     "two-bit one",2,"1"; "two-bit two",2,"2";
     "zero",32,"0"; "all ones",32,"0xffffffff";
     "signed minus two",8,"-2"; "signed minimum",8,"-128";
     "truncate unsigned",8,"0x123"; "truncate negative",8,"-257";
     "zero width",0,"19"; "wide literal",128,"0x123456789abcdef0011223344556677"];
  for width=0 to 12 do
    for value= -300 to 300 do
      check_literal "small signed/unsigned sweep" width (Z.of_int value)
    done
  done;
  Printf.printf "PASS: literal bit order, truncation, signed values and extracted NBits decoding.\n"

(* FIRRTL verification labels are module-local. The generated Coq definitions
   share a global namespace, so even equal labels must retain distinct goals. *)
let check_verification_names () =
  let source = {|FIRRTL version 1.2.0
circuit Top :
  module Child :
    input clock : Clock
    input enabled : UInt<1>
    assert(clock, enabled, UInt<1>("h1"), "") : same
    assume(clock, enabled, UInt<1>("h1"), "") : same
  module Top :
    input clock : Clock
    input enabled : UInt<1>
    inst child of Child
    child.clock <= clock
    child.enabled <= enabled
    assert(clock, enabled, UInt<1>("h1"), "") : same
    assume(clock, enabled, UInt<1>("h1"), "") : same
|} in
  let input = Filename.temp_file "verification-labels" ".fir" in
  let output = Filename.temp_file "verification-labels" ".v" in
  Fun.protect ~finally:(fun () -> Sys.remove input; Sys.remove output) (fun () ->
    let oc = open_out input in output_string oc source; close_out oc;
    let ast = Hifirrtl_lang.Parser.hiparse input in
    let ((modmap, _), maps) = Transhiast_without_inline.mapcir ast in
    let translated = Transhiast_without_inline.trans_cir ast modmap maps in
    if translated.top_reset <> None then failwith "invented a reset port";
    let oc = open_out output in Coqgen.emit_file oc translated; close_out oc;
    let ic = open_in output in
    let text = really_input_string ic (in_channel_length ic) in close_in ic;
    let definitions = String.split_on_char '\n' text |> List.filter_map (fun line ->
      match String.split_on_char ' ' line with
      | "Definition" :: name :: _ -> Some name
      | _ -> None) in
    let unique = List.sort_uniq String.compare definitions in
    if List.length definitions <> List.length unique then
      failwith "duplicate generated Coq definitions for module-local labels";
    List.iter (fun name -> if not (List.mem name definitions) then failwith ("missing " ^ name))
      ["generated_assert_m0_0_local"; "generated_assert_m1_1_local";
       "generated_assume_m0_0_local"; "generated_assume_m1_1_local";
       "generated_observe"; "generated_observe_cycle"];
    if List.length translated.assertions <> 2 || List.length translated.assumes <> 2 then
      failwith "module-local verification properties were lost")

let () =
  check_verification_names ();
  Printf.printf "PASS: module-local assert/assume labels produce distinct Coq definitions.\n"

let () =
  let source = {|FIRRTL version 1.2.0
circuit ResetMetadata :
  module ResetMetadata :
    input data0 : UInt<8>
    input data1 : UInt<8>
    input reset : UInt<1>
    input clock : Clock
|} in
  let input = Filename.temp_file "reset-metadata" ".fir" in
  Fun.protect ~finally:(fun () -> Sys.remove input) (fun () ->
    let oc = open_out input in output_string oc source; close_out oc;
    let ast = Hifirrtl_lang.Parser.hiparse input in
    let ((modmap, _), maps) = Transhiast_without_inline.mapcir ast in
    let translated = Transhiast_without_inline.trans_cir ast modmap maps in
    if translated.top_reset <> Some (2, Extraction.Env_with_implicit_widths.Fuint 1) then
      failwith "reset metadata did not follow the actual translated top port ID");
  Printf.printf "PASS: top reset metadata follows its declared name, type and translated ID.\n"
