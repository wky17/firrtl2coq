circuit CombWhen :
  module CombWhen :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip cond : UInt<1>, out : UInt<4>}

    wire w : UInt @[Combinational.scala 46:15]
    w <= UInt<1>("h0") @[Combinational.scala 48:5]
    when io.cond : @[Combinational.scala 49:15]
    {
      w <= UInt<2>("h3") @[Combinational.scala 50:7]
    }
    io.out <= w @[Combinational.scala 53:10]

