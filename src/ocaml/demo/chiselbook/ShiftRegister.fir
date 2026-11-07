circuit ShiftRegister :
  module ShiftRegister :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip din : UInt<1>, dout : UInt<1>, flip serIn : UInt<1>, paraOut : UInt<4>, flip d : UInt<4>, flip load : UInt<1>, serOut : UInt<1>}

    reg shiftReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), shiftReg) @[ShiftRegister.scala 18:21]
    node _shiftReg_T = bits(shiftReg, 2, 0) @[ShiftRegister.scala 19:23]
    node _shiftReg_T_1 = cat(_shiftReg_T, io.din) @[ShiftRegister.scala 19:30]
    shiftReg <= _shiftReg_T_1 @[ShiftRegister.scala 19:12]
    node dout = bits(shiftReg, 3, 3) @[ShiftRegister.scala 20:22]
    reg outReg : UInt<4>, clock with :
      reset => (reset1, UInt<4>("h0")) @[ShiftRegister.scala 28:23]
    node _outReg_T = bits(outReg, 3, 1) @[ShiftRegister.scala 29:28]
    node _outReg_T_1 = cat(io.serIn, _outReg_T) @[ShiftRegister.scala 29:19]
    outReg <= _outReg_T_1 @[ShiftRegister.scala 29:10]
    reg loadReg : UInt<4>, clock with :
      reset => (reset1, UInt<4>("h0")) @[ShiftRegister.scala 36:24]
    when io.load : @[ShiftRegister.scala 37:15]
    {
      loadReg <= io.d @[ShiftRegister.scala 38:13]
    }
    else :
    {
      node _loadReg_T = bits(loadReg, 3, 1) @[ShiftRegister.scala 40:30]
      node _loadReg_T_1 = cat(UInt<1>("h0"), _loadReg_T) @[ShiftRegister.scala 40:20]
      loadReg <= _loadReg_T_1 @[ShiftRegister.scala 40:13]
    }
    node serOut = bits(loadReg, 0, 0) @[ShiftRegister.scala 42:23]
    io.serOut <= serOut @[ShiftRegister.scala 45:13]
    io.paraOut <= outReg @[ShiftRegister.scala 47:14]
    io.dout <= dout @[ShiftRegister.scala 48:11]

