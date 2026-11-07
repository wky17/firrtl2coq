circuit test :
  module test :
    input en : UInt<1>
    output y : UInt<8>

    when en :
    {
      y <= UInt(1)
    }
    y <= UInt(0)              