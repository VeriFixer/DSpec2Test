
method {:test} Test7() {
expect 0 <= 1 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1073741824 as bv32), 1);
expect r0 == ((1073741824 as bv32) << 1 as bv6) | ((1073741824 as bv32) >> (32 - 1) as bv6);
}

// REPEAT 3 - TIME: 7.0825188 s