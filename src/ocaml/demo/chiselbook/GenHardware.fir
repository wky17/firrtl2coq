circuit GenHardware :
  module GenHardware :
    input clock_wky: Clock
    input reset1 : UInt<1>
    output io : { data : UInt<8>[12], len : UInt<8>, flip squareIn : UInt<8>, squareOut : UInt<8>}

    wire text : UInt<7>[12] @[GenHardware.scala 13:21]
    text[0] <= UInt<7>("h48") @[GenHardware.scala 13:21]
    text[1] <= UInt<7>("h65") @[GenHardware.scala 13:21]
    text[2] <= UInt<7>("h6c") @[GenHardware.scala 13:21]
    text[3] <= UInt<7>("h6c") @[GenHardware.scala 13:21]
    text[4] <= UInt<7>("h6f") @[GenHardware.scala 13:21]
    text[5] <= UInt<6>("h20") @[GenHardware.scala 13:21]
    text[6] <= UInt<7>("h57") @[GenHardware.scala 13:21]
    text[7] <= UInt<7>("h6f") @[GenHardware.scala 13:21]
    text[8] <= UInt<7>("h72") @[GenHardware.scala 13:21]
    text[9] <= UInt<7>("h6c") @[GenHardware.scala 13:21]
    text[10] <= UInt<7>("h64") @[GenHardware.scala 13:21]
    text[11] <= UInt<6>("h21") @[GenHardware.scala 13:21]
    wire squareROM : UInt<5>[6] @[GenHardware.scala 19:26]
    squareROM[0] <= UInt<1>("h0") @[GenHardware.scala 19:26]
    squareROM[1] <= UInt<1>("h1") @[GenHardware.scala 19:26]
    squareROM[2] <= UInt<3>("h4") @[GenHardware.scala 19:26]
    squareROM[3] <= UInt<4>("h9") @[GenHardware.scala 19:26]
    squareROM[4] <= UInt<5>("h10") @[GenHardware.scala 19:26]
    squareROM[5] <= UInt<5>("h19") @[GenHardware.scala 19:26]
    node _square_T = bits(io.squareIn, 2, 0)
    io.data <= text @[GenHardware.scala 25:11]
    io.len <= UInt<4>("hc") @[GenHardware.scala 26:10]
    io.squareOut <= squareROM[_square_T] @[GenHardware.scala 27:16]

