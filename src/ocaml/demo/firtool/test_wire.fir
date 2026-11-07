; RUN: firtool --split-input-file %s | FileCheck %s

; CHECK-LABEL: module test_wire(
FIRRTL version 3.3.0
circuit test_wire :
  module test_wire :
    input clock : Clock
    input r : AsyncReset
    input in : { foo : UInt<8>, bar : UInt<8>}
    output out : { foo : UInt<8>, bar : UInt<8>}

    node reset_wky= r

    wire reg1_w : { foo : UInt<8>, bar : UInt<8>}
    invalidate reg1_w.bar
    invalidate reg1_w.foo
    ; CHECK: reg1_foo <= 8'hC;
    ; CHECK: reg1_bar <= 8'h0;
    connect reg1_w.foo, UInt<8>("hc")
    invalidate reg1_w.bar
    ; CHECK: reg1_foo = 8'hC;
    ; CHECK: reg1_bar = 8'h0;
    regreset reg1 : { foo : UInt<8>, bar : UInt<8>}, clock, reset_wky, reg1_w
    wire reg2 : { foo : UInt<8>, bar : UInt<8>}
    connect reg1, in
    connect reg2, reg1
    connect out, reg2

