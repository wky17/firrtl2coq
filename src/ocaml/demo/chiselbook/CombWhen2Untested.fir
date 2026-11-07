circuit CombWhen2Untested :
  module CombWhen2Untested :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip data : UInt<4>, out : UInt<1>}

    wire enoughMoney : UInt<1> @[Combinational.scala 69:25]
    enoughMoney <= UInt<1>("h0") @[Combinational.scala 71:15]
    node _T = geq(io.data, UInt<3>("h5")) @[Combinational.scala 72:17]
    when _T : @[Combinational.scala 72:27]
    {
      enoughMoney <= UInt<1>("h1") @[Combinational.scala 73:17]
    }
    io.out <= enoughMoney @[Combinational.scala 76:10]

