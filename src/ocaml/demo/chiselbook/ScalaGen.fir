circuit ScalaGen :
  module ScalaGen :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip din : UInt<1>, dout : UInt<8>}

    reg regVec : UInt<1>[8], clock with :
      reset => (UInt<1>("h0"), regVec) @[ScalaGen.scala 10:19]
    regVec[0] <= io.din @[ScalaGen.scala 12:13]
    regVec[1] <= regVec[0] @[ScalaGen.scala 14:15]
    regVec[2] <= regVec[1] @[ScalaGen.scala 14:15]
    regVec[3] <= regVec[2] @[ScalaGen.scala 14:15]
    regVec[4] <= regVec[3] @[ScalaGen.scala 14:15]
    regVec[5] <= regVec[4] @[ScalaGen.scala 14:15]
    regVec[6] <= regVec[5] @[ScalaGen.scala 14:15]
    regVec[7] <= regVec[6] @[ScalaGen.scala 14:15]
    node io_dout_lo_lo = cat(regVec[1], regVec[0]) @[ScalaGen.scala 18:21]
    node io_dout_lo_hi = cat(regVec[3], regVec[2]) @[ScalaGen.scala 18:21]
    node io_dout_lo = cat(io_dout_lo_hi, io_dout_lo_lo) @[ScalaGen.scala 18:21]
    node io_dout_hi_lo = cat(regVec[5], regVec[4]) @[ScalaGen.scala 18:21]
    node io_dout_hi_hi = cat(regVec[7], regVec[6]) @[ScalaGen.scala 18:21]
    node io_dout_hi = cat(io_dout_hi_hi, io_dout_hi_lo) @[ScalaGen.scala 18:21]
    node _io_dout_T = cat(io_dout_hi, io_dout_lo) @[ScalaGen.scala 18:21]
    io.dout <= _io_dout_T @[ScalaGen.scala 18:11]

