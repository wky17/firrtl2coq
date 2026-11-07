circuit Foo:
  module Foo:
    input clock: Clock
    input reset_wky: UInt<1>
    input a_d: UInt<1>[2]
    output a_q: UInt<1>[2]

    wire init: UInt<1>[2]
    init[0] <= UInt<1>(0)
    init[1] <= UInt<1>(0)

    reg r: UInt<1>[2], clock with:
      reset => (reset_wky, init)

    r <= a_d
    a_q <= r