circuit BubbleFifo :
  module FifoRegister :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_1 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_2 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_3 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_4 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_5 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_6 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_7 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_8 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module FifoRegister_9 :
    input clock: Clock
    input reset_wky: Reset
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    reg stateReg : UInt<1>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[BubbleFifo.scala 63:24]
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

  module BubbleFifo :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { enq : { flip write : UInt<1>, full : UInt<1>, flip din : UInt<8>}, deq : { flip read : UInt<1>, empty : UInt<1>, dout : UInt<8>}}

    inst FifoRegister aof FifoRegister @[BubbleFifo.scala 99:43]
    FifoRegister.clock <= clock
    FifoRegister.reset_wky <= reset_wky
    inst FifoRegister_1 aof FifoRegister_1 @[BubbleFifo.scala 99:43]
    FifoRegister_1.clock <= clock
    FifoRegister_1.reset_wky <= reset_wky
    inst FifoRegister_2 aof FifoRegister_2 @[BubbleFifo.scala 99:43]
    FifoRegister_2.clock <= clock
    FifoRegister_2.reset_wky <= reset_wky
    inst FifoRegister_3 aof FifoRegister_3 @[BubbleFifo.scala 99:43]
    FifoRegister_3.clock <= clock
    FifoRegister_3.reset_wky <= reset_wky
    inst FifoRegister_4 aof FifoRegister_4 @[BubbleFifo.scala 99:43]
    FifoRegister_4.clock <= clock
    FifoRegister_4.reset_wky <= reset_wky
    inst FifoRegister_5 aof FifoRegister_5 @[BubbleFifo.scala 99:43]
    FifoRegister_5.clock <= clock
    FifoRegister_5.reset_wky <= reset_wky
    inst FifoRegister_6 aof FifoRegister_6 @[BubbleFifo.scala 99:43]
    FifoRegister_6.clock <= clock
    FifoRegister_6.reset_wky <= reset_wky
    inst FifoRegister_7 aof FifoRegister_7 @[BubbleFifo.scala 99:43]
    FifoRegister_7.clock <= clock
    FifoRegister_7.reset_wky <= reset_wky
    inst FifoRegister_8 aof FifoRegister_8 @[BubbleFifo.scala 99:43]
    FifoRegister_8.clock <= clock
    FifoRegister_8.reset_wky <= reset_wky
    inst FifoRegister_9 aof FifoRegister_9 @[BubbleFifo.scala 99:43]
    FifoRegister_9.clock <= clock
    FifoRegister_9.reset_wky <= reset_wky
    FifoRegister_1.io.enq.din <= FifoRegister.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T = not(FifoRegister.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_1.io.enq.write <= _T @[BubbleFifo.scala 102:33]
    node _T_1 = not(FifoRegister_1.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister.io.deq.read <= _T_1 @[BubbleFifo.scala 103:28]
    FifoRegister_2.io.enq.din <= FifoRegister_1.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_2 = not(FifoRegister_1.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_2.io.enq.write <= _T_2 @[BubbleFifo.scala 102:33]
    node _T_3 = not(FifoRegister_2.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_1.io.deq.read <= _T_3 @[BubbleFifo.scala 103:28]
    FifoRegister_3.io.enq.din <= FifoRegister_2.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_4 = not(FifoRegister_2.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_3.io.enq.write <= _T_4 @[BubbleFifo.scala 102:33]
    node _T_5 = not(FifoRegister_3.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_2.io.deq.read <= _T_5 @[BubbleFifo.scala 103:28]
    FifoRegister_4.io.enq.din <= FifoRegister_3.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_6 = not(FifoRegister_3.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_4.io.enq.write <= _T_6 @[BubbleFifo.scala 102:33]
    node _T_7 = not(FifoRegister_4.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_3.io.deq.read <= _T_7 @[BubbleFifo.scala 103:28]
    FifoRegister_5.io.enq.din <= FifoRegister_4.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_8 = not(FifoRegister_4.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_5.io.enq.write <= _T_8 @[BubbleFifo.scala 102:33]
    node _T_9 = not(FifoRegister_5.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_4.io.deq.read <= _T_9 @[BubbleFifo.scala 103:28]
    FifoRegister_6.io.enq.din <= FifoRegister_5.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_10 = not(FifoRegister_5.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_6.io.enq.write <= _T_10 @[BubbleFifo.scala 102:33]
    node _T_11 = not(FifoRegister_6.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_5.io.deq.read <= _T_11 @[BubbleFifo.scala 103:28]
    FifoRegister_7.io.enq.din <= FifoRegister_6.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_12 = not(FifoRegister_6.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_7.io.enq.write <= _T_12 @[BubbleFifo.scala 102:33]
    node _T_13 = not(FifoRegister_7.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_6.io.deq.read <= _T_13 @[BubbleFifo.scala 103:28]
    FifoRegister_8.io.enq.din <= FifoRegister_7.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_14 = not(FifoRegister_7.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_8.io.enq.write <= _T_14 @[BubbleFifo.scala 102:33]
    node _T_15 = not(FifoRegister_8.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_7.io.deq.read <= _T_15 @[BubbleFifo.scala 103:28]
    FifoRegister_9.io.enq.din <= FifoRegister_8.io.deq.dout @[BubbleFifo.scala 101:31]
    node _T_16 = not(FifoRegister_8.io.deq.empty) @[BubbleFifo.scala 102:36]
    FifoRegister_9.io.enq.write <= _T_16 @[BubbleFifo.scala 102:33]
    node _T_17 = not(FifoRegister_9.io.enq.full) @[BubbleFifo.scala 103:31]
    FifoRegister_8.io.deq.read <= _T_17 @[BubbleFifo.scala 103:28]
    FifoRegister.io.enq.din <= io.enq.din @[BubbleFifo.scala 105:10]
    io.enq.full <= FifoRegister.io.enq.full @[BubbleFifo.scala 105:10]
    FifoRegister.io.enq.write <= io.enq.write @[BubbleFifo.scala 105:10]
    io.deq.dout <= FifoRegister_9.io.deq.dout @[BubbleFifo.scala 106:10]
    io.deq.empty <= FifoRegister_9.io.deq.empty @[BubbleFifo.scala 106:10]
    FifoRegister_9.io.deq.read <= io.deq.read @[BubbleFifo.scala 106:10]

