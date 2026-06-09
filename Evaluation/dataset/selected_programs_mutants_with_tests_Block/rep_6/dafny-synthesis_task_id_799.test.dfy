
method {:test} Test5() {
expect 0 <= 6 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2684354560 as bv32), 6);
expect r0 == ((2684354560 as bv32) << 6 as bv6) | ((2684354560 as bv32) >> (32 - 6) as bv6);
}

// REPEAT 6 - TIME: 5.6941544 s