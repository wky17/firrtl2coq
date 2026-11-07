; RUN: firtool %s --format=fir --parse-only --split-input-file | FileCheck %s

; Ensure connect is demoted to partial connect in the presence of implicit truncation.

; CHECK-LABEL: @truncatingIntegerConnect
; CHECK: %0 = firrtl.tail_wky %b, 2 : (!firrtl.uint<5>) -> !firrtl.uint<3>
; CHECK: firrtl.matchingconnect %a, %0 : !firrtl.uint<3>
FIRRTL version 4.0.0
circuit truncatingIntegerConnect :
 public module truncatingIntegerConnect :
   output a: UInt<3>
   input b: UInt<5>
   connect a, b

