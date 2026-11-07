circuit Foo :
  module Foo :
    input a: { b: {c: UInt<1>}}
    output b: { b: {c: UInt<1>}}

    b <= a