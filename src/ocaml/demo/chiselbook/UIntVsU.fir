circuit UIntVsU :
  module UIntVsU :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { values : UInt<3>[5]}

    io.values[0] <= UInt<3>("h7") @[UIntVsU.scala 10:8]
    io.values[1] <= UInt<3>("h7") @[UIntVsU.scala 11:8]
    io.values[2] <= UInt<3>("h7") @[UIntVsU.scala 13:8]
    io.values[3] <= UInt<3>("h7") @[UIntVsU.scala 14:8]
    wire signed : SInt<3> @[UIntVsU.scala 15:27]
    signed <= asSInt(UInt<3>("h7")) @[UIntVsU.scala 15:27]
    node _io_values_4_T = asUInt(signed) @[UIntVsU.scala 16:18]
    io.values[4] <= _io_values_4_T @[UIntVsU.scala 16:8]

