circuit Foo:
  module Foo:
    input clock: Clock
    input a_d: UInt<1>[2]
    output a_q: UInt<1>[2]

    reg r: UInt<1>[2], clock
    r <= a_d
    a_q <= r