circuit Arbiter3Loop :
  module Arbiter3Loop :
    input clock_wky: Clock
    input reset1 : UInt<1>
    output io : { flip request : UInt<3>, grant : UInt<3>}

    node _request_T = bits(io.request, 0, 0) @[arbiter.scala 65:36]
    node _request_T_1 = bits(io.request, 1, 1) @[arbiter.scala 65:36]
    node _request_T_2 = bits(io.request, 2, 2) @[arbiter.scala 65:36]
    wire request : UInt<1>[3] @[arbiter.scala 65:24]
    request[0] <= _request_T @[arbiter.scala 65:24]
    request[1] <= _request_T_1 @[arbiter.scala 65:24]
    request[2] <= _request_T_2 @[arbiter.scala 65:24]
    wire grant : UInt<1>[3] @[arbiter.scala 69:30]
    grant[0] <= UInt<1>("h0") @[arbiter.scala 69:30]
    grant[1] <= UInt<1>("h0") @[arbiter.scala 69:30]
    grant[2] <= UInt<1>("h0") @[arbiter.scala 69:30]
    wire notGranted : UInt<1>[3] @[arbiter.scala 70:35]
    notGranted[0] <= UInt<1>("h0") @[arbiter.scala 70:35]
    notGranted[1] <= UInt<1>("h0") @[arbiter.scala 70:35]
    notGranted[2] <= UInt<1>("h0") @[arbiter.scala 70:35]
    grant[0] <= request[0] @[arbiter.scala 72:12]
    node _notGranted_0_T = eq(grant[0], UInt<1>("h0")) @[arbiter.scala 73:20]
    notGranted[0] <= _notGranted_0_T @[arbiter.scala 73:17]
    node _grant_1_T = and(request[1], notGranted[0]) @[arbiter.scala 75:28]
    grant[1] <= _grant_1_T @[arbiter.scala 75:14]
    node _notGranted_1_T = eq(grant[1], UInt<1>("h0")) @[arbiter.scala 76:22]
    node _notGranted_1_T_1 = and(_notGranted_1_T, notGranted[0]) @[arbiter.scala 76:32]
    notGranted[1] <= _notGranted_1_T_1 @[arbiter.scala 76:19]
    node _grant_2_T = and(request[2], notGranted[1]) @[arbiter.scala 75:28]
    grant[2] <= _grant_2_T @[arbiter.scala 75:14]
    node _notGranted_2_T = eq(grant[2], UInt<1>("h0")) @[arbiter.scala 76:22]
    node _notGranted_2_T_1 = and(_notGranted_2_T, notGranted[1]) @[arbiter.scala 76:32]
    notGranted[2] <= _notGranted_2_T_1 @[arbiter.scala 76:19]
    node io_grant_hi = cat(grant[2], grant[1]) @[arbiter.scala 80:21]
    node _io_grant_T = cat(io_grant_hi, grant[0]) @[arbiter.scala 80:21]
    io.grant <= _io_grant_T @[arbiter.scala 80:12]

