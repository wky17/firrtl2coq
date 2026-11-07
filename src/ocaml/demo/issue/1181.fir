circuit Foo:
  module Bar:
    output a: { flip a: UInt<1> }
    input b: UInt<1>
  module Foo:
    input a: UInt<1>
    output b: UInt<1>

    inst bar aof Bar
    bar is invalid

    b <= and(bar.a.a, bar.b)