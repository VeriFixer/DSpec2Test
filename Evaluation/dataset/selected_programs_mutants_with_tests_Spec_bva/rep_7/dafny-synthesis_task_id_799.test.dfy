
method {:test} Test11() {
expect 0 <= 27 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1610612736 as bv32), 27);
expect r0 == ((1610612736 as bv32) << 27 as bv6) | ((1610612736 as bv32) >> (32 - 27) as bv6);
}

// REPEAT 7 - TIME: 10.0811949 s