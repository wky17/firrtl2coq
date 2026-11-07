; RUN: firtool %s --format=fir --parse-only --split-input-file | FileCheck %s

; Ensure connect is demoted to partial connect in the presence of implicit truncation.

; CHECK-LABEL: @regularConnect
; CHECK: %0 = firrtl.pad_wky %b, 5 : (!firrtl.uint<3>) -> !firrtl.uint<5>
; CHECK: firrtl.matchingconnect %a, %0 : !firrtl.uint<5>
FIRRTL version 4.0.0
circuit regularConnect :
 public module regularConnect :
   output a: UInt<5>
   input b: UInt<3>
   connect a, b

