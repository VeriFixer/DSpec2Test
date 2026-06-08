
method {:test} Test6() {
expect 0 <= 30 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2147483648 as bv32), 30);
expect r0 == ((2147483648 as bv32) << 30 as bv6) | ((2147483648 as bv32) >> (32 - 30) as bv6);
}

// REPEAT 2 - TIME: 6.7421597 s