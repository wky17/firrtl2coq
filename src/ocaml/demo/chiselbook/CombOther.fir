circuit CombOther :
  module CombOther :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip cond : UInt<1>, out : UInt<4>}

    wire w : UInt @[Combinational.scala 91:15]
    when io.cond : @[Combinational.scala 93:15]
    {
      w <= UInt<1>("h1") @[Combinational.scala 94:7]
    }
    else :
    {
      w <= UInt<2>("h2") @[Combinational.scala 96:7]
    }
    io.out <= w @[Combinational.scala 99:10]

