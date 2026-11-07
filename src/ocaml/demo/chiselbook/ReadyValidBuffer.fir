circuit ReadyValidBuffer :
  module ReadyValidBuffer :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip in : { flip ready : UInt<1>, valid : UInt<1>, bits1 : UInt<8>}, out : { flip ready : UInt<1>, valid : UInt<1>, bits1 : UInt<8>}}

    reg dataReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), dataReg) @[ReadyValidBuffer.scala 11:20]
    reg emptyReg : UInt<1>, clock with :
      reset => (reset1, UInt<1>("h1")) @[ReadyValidBuffer.scala 12:25]
    io.in.ready <= emptyReg @[ReadyValidBuffer.scala 14:15]
    node _io_out_valid_T = eq(emptyReg, UInt<1>("h0")) @[ReadyValidBuffer.scala 15:19]
    io.out.valid <= _io_out_valid_T @[ReadyValidBuffer.scala 15:16]
    io.out.bits1 <= dataReg @[ReadyValidBuffer.scala 16:15]
    node _T = and(emptyReg, io.in.valid) @[ReadyValidBuffer.scala 18:18]
    when _T : @[ReadyValidBuffer.scala 18:33]
    {
      dataReg <= io.in.bits1 @[ReadyValidBuffer.scala 19:13]
      emptyReg <= UInt<1>("h0") @[ReadyValidBuffer.scala 20:14]
    }
    node _T_1 = eq(emptyReg, UInt<1>("h0")) @[ReadyValidBuffer.scala 23:9]
    node _T_2 = and(_T_1, io.out.ready) @[ReadyValidBuffer.scala 23:19]
    when _T_2 : @[ReadyValidBuffer.scala 23:35]
    {
      emptyReg <= UInt<1>("h1") @[ReadyValidBuffer.scala 24:14]
 }


