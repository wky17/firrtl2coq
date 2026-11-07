circuit Queue_4:
  module Queue_4:
    input a : { data: UInt<512>, strb: UInt<64>, last: UInt<1> }
    output b : { data: UInt<512>, strb: UInt<64>, last: UInt<1> }

    b <= a
