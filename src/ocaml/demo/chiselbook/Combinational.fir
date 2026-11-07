circuit Combinational :
  module Combinational :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip a : UInt<4>, flip b : UInt<4>, flip c : UInt<4>, out : UInt<4>, out2 : UInt<4>}

    node _e_T = and(io.a, io.b) @[Combinational.scala 17:14]
    node e = or(_e_T, io.c) @[Combinational.scala 17:19]
    node f = not(e) @[Combinational.scala 21:11]
    io.out <= e @[Combinational.scala 30:10]
    io.out2 <= f @[Combinational.scala 31:11]

