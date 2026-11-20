FIRRTL version 1.2.0
circuit MixedSnapshotObservation :
  module MixedSnapshotObservation :
    input clock : Clock
    input reset : UInt<1>
    input permit : UInt<1>
    output outValid : UInt<1>
    output outData : UInt<1>
    reg wasStalled : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0"))
    reg previousOutput : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0"))
    node same = eq(outData, previousOutput)
    outValid <= UInt<1>("h1")
    outData <= UInt<1>("h1")
    wasStalled <= outValid
    previousOutput <= outData
    assert(clock, same, wasStalled, "") : assert
    assume(clock, permit, UInt<1>("h1"), "") : assume
