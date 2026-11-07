circuit CombWireDefault :
  module CombWireDefault :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip cond : UInt<1>, out : UInt<4>}

    wire w : UInt @[Combinational.scala 142:22]
    w <= UInt<1>("h0") @[Combinational.scala 142:22]
    when io.cond : @[Combinational.scala 144:15]
    {
      w <= UInt<2>("h3") @[Combinational.scala 145:7]
    }
    io.out <= w @[Combinational.scala 149:10]

