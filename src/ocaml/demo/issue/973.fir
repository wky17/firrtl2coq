circuit f973Foo :
  module f973Foo :
  
    wire x : UInt<1> @[f973.scala 11:17]
    when UInt<1>("h1") : @[f973.scala 12:19]
    {
      x <= UInt<1>("h0") @[f973.scala 12:23]
    }
    x <= UInt<1>("h1") @[f973.scala 13:7]
    