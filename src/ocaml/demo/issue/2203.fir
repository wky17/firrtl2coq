circuit Foo:
  module Foo:
    input clock: Clock
    output a: UInt<1>

    wire x: SInt<1>
    x is invalid

    reg b: UInt<1>, clock
    b <= asUInt(x)
    a <= b