circuit Foo:
  module Bar:
    input a: { a: UInt<1> }
    output b: { a: UInt<1> }
    b <= a

  module Foo:
    input a: { a: UInt<1> }
    output b: { a: UInt<1> }
    inst bar aof Bar
    bar.a <= a
    b <= bar.b