
method {:test} Test6() {
expect 0 <= 5 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1610612736 as bv32), 5);
expect r0 == ((1610612736 as bv32) << 5 as bv6) | ((1610612736 as bv32) >> (32 - 5) as bv6);
}

// REPEAT 7 - TIME: 5.4104854 s