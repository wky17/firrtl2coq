circuit Foo:
  module Foo:
    input a: {a: UInt<2>}
    output b: {a: UInt<1>}

    b <= a