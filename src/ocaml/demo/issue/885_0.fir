circuit MyModule :
  module MyModule :
    input en: UInt<1>
    input a: UInt<1>
    input b: UInt<1>
    wire w: UInt<1>
    when en :
    {
      w <= a
    }
    else :
    {
      w <= b     }
