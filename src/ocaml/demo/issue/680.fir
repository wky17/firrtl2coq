circuit Foo :
  module Foo:
    input a: {a: UInt<1>}
    output b: {a: UInt<1>}

    wire x: {a: UInt<1>}

    x.a <= a.a
    b.a <= x.a