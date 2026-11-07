circuit Queue_9:
  module Queue_9:
    input a : { addr: UInt<25>, len: UInt<8>, size: UInt<3>, burst: UInt<2>, lock: UInt<1>, cache: UInt<4>, prot: UInt<3>, qos: UInt<4>, region: UInt<4>, id: UInt<12>, user: UInt<1> }
    output b : { addr: UInt<25>, len: UInt<8>, size: UInt<3>, burst: UInt<2>, lock: UInt<1>, cache: UInt<4>, prot: UInt<3>, qos: UInt<4>, region: UInt<4>, id: UInt<12>, user: UInt<1> }

    b <= a