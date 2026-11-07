circuit CountAndDriver :
  module CountAndDriver :
    input reset0 : UInt<1>
    input reset1 : UInt<1>
    input in0 : UInt<4>
    input in1 : UInt<4>
    output out1 : UInt<4>

    out1 <= in0
    when reset0 :
    {
      when reset1 :
      {
        out1 <= in1      }
    }
