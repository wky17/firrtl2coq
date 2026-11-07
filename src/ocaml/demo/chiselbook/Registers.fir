circuit Registers :
  module Registers :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip in : UInt<8>, out : UInt<8>}

    reg q : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Registers.scala 10:20]
    q <= io.in @[Registers.scala 15:7]
    reg nextReg : UInt, clock with :
      reset => (UInt<1>("h0"), q) @[Registers.scala 20:24]
    nextReg <= io.in @[Registers.scala 20:24]
    reg bothReg : UInt, clock with :
      reset => (reset1, UInt<1>("h0")) @[Registers.scala 24:24]
    bothReg <= io.in @[Registers.scala 24:24]
    io.out <= q @[Registers.scala 26:10]

