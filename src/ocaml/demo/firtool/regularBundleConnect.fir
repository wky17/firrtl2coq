; RUN: firtool %s --format=fir --parse-only --split-input-file | FileCheck %s

; Ensure connect is demoted to partial connect in the presence of implicit truncation.

; CHECK-LABEL: @regularBundleConnect
; CHECK: %0 = firrtl.subfield %a[a] : !firrtl.bundle<a: uint<5>, b: uint<3>>
; CHECK: %1 = firrtl.subfield %b[a] : !firrtl.bundle<a: uint<3>, b: uint<2>>
; CHECK: %2 = firrtl.pad_wky %1, 5 : (!firrtl.uint<3>) -> !firrtl.uint<5>
; CHECK: firrtl.matchingconnect %0, %2 : !firrtl.uint<5>
; CHECK: %3 = firrtl.subfield %a[b] : !firrtl.bundle<a: uint<5>, b: uint<3>>
; CHECK: %4 = firrtl.subfield %b[b] : !firrtl.bundle<a: uint<3>, b: uint<2>>
; CHECK: %5 = firrtl.pad_wky %4, 3 : (!firrtl.uint<2>) -> !firrtl.uint<3>
; CHECK: firrtl.matchingconnect %3, %5 : !firrtl.uint<3>
FIRRTL version 4.0.0
circuit regularBundleConnect :
 public module regularBundleConnect :
   output a: { a: UInt<5>, b: UInt<3> }
   input b: { a: UInt<3>, b: UInt<2> }
   connect a, b
