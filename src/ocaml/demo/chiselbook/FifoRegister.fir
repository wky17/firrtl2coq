circuit FifoRegister :
  module FifoRegister :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<10>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<10>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset1, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<10>, clock with :
      reset => (reset1, UInt<10>("h0")) @[BubbleFifo.scala 63:24]
    node _T = eq(stateReg, UInt<1>("h0")) @[BubbleFifo.scala 65:17]
    when _T : @[BubbleFifo.scala 65:28]
    {
      when io.enq.write : @[BubbleFifo.scala 66:24]
      {
        stateReg <= UInt<1>("h1") @[BubbleFifo.scala 67:16]
        dataReg <= io.enq.din @[BubbleFifo.scala 68:15]
    }
    }
    else :
    {
      node _T_1 = eq(stateReg, UInt<1>("h1")) @[BubbleFifo.scala 70:23]
      when _T_1 : @[BubbleFifo.scala 70:33]
      {
        when io.deq.read : @[BubbleFifo.scala 71:23]
        {
          stateReg <= UInt<1>("h0") @[BubbleFifo.scala 72:16]
          dataReg <= UInt<1>("h0") @[BubbleFifo.scala 73:15]
      }
      }
      else :
      {
        skip
    }
    }
    node _io_enq_full_T = eq(stateReg, UInt<1>("h1")) @[BubbleFifo.scala 79:28]
    io.enq.full <= _io_enq_full_T @[BubbleFifo.scala 79:15]
    node _io_deq_empty_T = eq(stateReg, UInt<1>("h0")) @[BubbleFifo.scala 80:29]
    io.deq.empty <= _io_deq_empty_T @[BubbleFifo.scala 80:16]
    io.deq.dout <= dataReg @[BubbleFifo.scala 81:15]

