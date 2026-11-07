circuit FunctionCounter :
  module FunctionCounter :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg count10 : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Counter.scala 77:25]
    node _count10_cntReg_T = eq(count10, UInt<4>("ha")) @[Counter.scala 78:26]
    node _count10_cntReg_T_1 = add(count10, UInt<1>("h1")) @[Counter.scala 78:47]
    node _count10_cntReg_T_2 = tail(_count10_cntReg_T_1, 1) @[Counter.scala 78:47]
    node _count10_cntReg_T_3 = mux(_count10_cntReg_T, UInt<1>("h0"), _count10_cntReg_T_2) @[Counter.scala 78:18]
    count10 <= _count10_cntReg_T_3 @[Counter.scala 78:12]
    reg count99 : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Counter.scala 77:25]
    node _count99_cntReg_T = eq(count99, UInt<7>("h63")) @[Counter.scala 78:26]
    node _count99_cntReg_T_1 = add(count99, UInt<1>("h1")) @[Counter.scala 78:47]
    node _count99_cntReg_T_2 = tail(_count99_cntReg_T_1, 1) @[Counter.scala 78:47]
    node _count99_cntReg_T_3 = mux(_count99_cntReg_T, UInt<1>("h0"), _count99_cntReg_T_2) @[Counter.scala 78:18]
    count99 <= _count99_cntReg_T_3 @[Counter.scala 78:12]
    reg testCounter : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Counter.scala 77:25]
    node _testCounter_cntReg_T = eq(testCounter, UInt<4>("h9")) @[Counter.scala 78:26]
    node _testCounter_cntReg_T_1 = add(testCounter, UInt<1>("h1")) @[Counter.scala 78:47]
    node _testCounter_cntReg_T_2 = tail(_testCounter_cntReg_T_1, 1) @[Counter.scala 78:47]
    node _testCounter_cntReg_T_3 = mux(_testCounter_cntReg_T, UInt<1>("h0"), _testCounter_cntReg_T_2) @[Counter.scala 78:18]
    testCounter <= _testCounter_cntReg_T_3 @[Counter.scala 78:12]
    node _io_tick_T = eq(testCounter, UInt<4>("h9")) @[Counter.scala 89:26]
    io.tick <= _io_tick_T @[Counter.scala 89:11]
    io.cnt <= testCounter @[Counter.scala 90:10]

