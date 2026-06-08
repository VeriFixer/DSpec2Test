
method {:test} Test12() {
expect 0 <= 26 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3758096384 as bv32), 26);
expect r0 == ((3758096384 as bv32) << 26 as bv6) | ((3758096384 as bv32) >> (32 - 26) as bv6);
}

// REPEAT 8 - TIME: 10.7506767 s