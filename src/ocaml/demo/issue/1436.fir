circuit FOO:
  module BAR:
    output io : { flip llWakeup : UInt<1>[1] }

  module FOO:
    inst thing aof BAR
    thing.io.llWakeup[0] <= UInt<1>(0)
    