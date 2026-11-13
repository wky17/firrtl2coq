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
