circuit Foo:
  module Foo:
    input x: UInt<10>[5]
    input source: UInt<2>
    output z: UInt<10>

    z <= x[source]