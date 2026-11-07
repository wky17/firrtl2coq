circuit Comparator :
  module Comparator :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip a : UInt<8>, flip b : UInt<8>, equ : UInt<1>, gt1 : UInt<1>}

    node equ = eq(io.a, io.b) @[Comparator.scala 15:15]
    node gt1 = gt(io.a, io.b) @[Comparator.scala 16:14]
    io.equ <= equ @[Comparator.scala 18:10]
    io.gt1 <= gt1 @[Comparator.scala 19:9]

