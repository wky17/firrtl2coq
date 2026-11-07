circuit Arbiter3 :
  module Arbiter3 :
    input clock_wky: Clock
    input reset1 : UInt<1>
    output io : { flip request : UInt<3>, grant : UInt<3>}

    node _request_T = bits(io.request, 0, 0) @[arbiter.scala 11:36]
    node _request_T_1 = bits(io.request, 1, 1) @[arbiter.scala 11:36]
    node _request_T_2 = bits(io.request, 2, 2) @[arbiter.scala 11:36]
    wire request : UInt<1>[3] @[arbiter.scala 11:24]
    request[0] <= _request_T @[arbiter.scala 11:24]
    request[1] <= _request_T_1 @[arbiter.scala 11:24]
    request[2] <= _request_T_2 @[arbiter.scala 11:24]
    wire grant : UInt<1>[3] @[arbiter.scala 14:22]
    grant[0] <= UInt<1>("h0") @[arbiter.scala 14:22]
    grant[1] <= UInt<1>("h0") @[arbiter.scala 14:22]
    grant[2] <= UInt<1>("h0") @[arbiter.scala 14:22]
    wire notGranted : UInt<1>[2] @[arbiter.scala 15:27]
    notGranted[0] <= UInt<1>("h0") @[arbiter.scala 15:27]
    notGranted[1] <= UInt<1>("h0") @[arbiter.scala 15:27]
    grant[0] <= request[0] @[arbiter.scala 17:12]
    node _notGranted_0_T = eq(grant[0], UInt<1>("h0")) @[arbiter.scala 18:20]
    notGranted[0] <= _notGranted_0_T @[arbiter.scala 18:17]
    node _grant_1_T = and(request[1], notGranted[0]) @[arbiter.scala 19:26]
    grant[1] <= _grant_1_T @[arbiter.scala 19:12]
    node _notGranted_1_T = eq(grant[1], UInt<1>("h0")) @[arbiter.scala 20:20]
    node _notGranted_1_T_1 = and(_notGranted_1_T, notGranted[0]) @[arbiter.scala 20:30]
    notGranted[1] <= _notGranted_1_T_1 @[arbiter.scala 20:17]
    node _grant_2_T = and(request[2], notGranted[1]) @[arbiter.scala 21:26]
    grant[2] <= _grant_2_T @[arbiter.scala 21:12]
    node io_grant_hi = cat(grant[2], grant[1]) @[arbiter.scala 24:21]
    node _io_grant_T = cat(io_grant_hi, grant[0]) @[arbiter.scala 24:21]
    io.grant <= _io_grant_T @[arbiter.scala 24:12]

