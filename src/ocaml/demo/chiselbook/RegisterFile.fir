circuit RegisterFile :
  module RegisterFile :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip rs1 : UInt<5>, flip rs2 : UInt<5>, flip rd : UInt<5>, flip wrData : UInt<32>, flip wrEna : UInt<1>, rs1Val : UInt<32>, rs2Val : UInt<32>, dbgPort : UInt<32>[32]}

    wire _regfile_WIRE : UInt<32>[32] @[RegisterFile.scala 15:32]
    _regfile_WIRE[0] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[1] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[2] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[3] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[4] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[5] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[6] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[7] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[8] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[9] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[10] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[11] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[12] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[13] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[14] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[15] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[16] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[17] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[18] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[19] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[20] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[21] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[22] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[23] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[24] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[25] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[26] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[27] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[28] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[29] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[30] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    _regfile_WIRE[31] <= UInt<32>("h0") @[RegisterFile.scala 15:32]
    reg regfile : UInt<32>[32], clock with :
      reset => (reset_wky, _regfile_WIRE) @[RegisterFile.scala 15:24]
    io.rs1Val <= regfile[io.rs1] @[RegisterFile.scala 16:13]
    io.rs2Val <= regfile[io.rs2] @[RegisterFile.scala 17:13]
    when io.wrEna : @[RegisterFile.scala 18:18]
    {
      regfile[io.rd] <= io.wrData @[RegisterFile.scala 19:20]
    }
    io.dbgPort <= regfile @[RegisterFile.scala 22:20]

