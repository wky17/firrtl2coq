circuit Timer :
  module Timer :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip din : UInt<8>, flip load : UInt<1>, done : UInt<1>}

    reg cntReg : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Timer.scala 13:23]
    node done = eq(cntReg, UInt<1>("h0")) @[Timer.scala 14:21]
    wire next : UInt @[Timer.scala 16:25]
    next <= UInt<1>("h0") @[Timer.scala 16:25]
    when io.load : @[Timer.scala 17:15]
    {
      next <= io.din @[Timer.scala 18:10]
    }
    else :
    {
      node _T = eq(done, UInt<1>("h0")) @[Timer.scala 19:16]
      when _T : @[Timer.scala 19:23]
      {
        node _next_T = sub(cntReg, UInt<1>("h1")) @[Timer.scala 20:20]
        node _next_T_1 = tail(_next_T, 1) @[Timer.scala 20:20]
        next <= _next_T_1 @[Timer.scala 20:10]
    }
    }
    cntReg <= next @[Timer.scala 22:10]
    io.done <= done @[Timer.scala 26:11]

