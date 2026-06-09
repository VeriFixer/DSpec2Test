
method {:test} Test7() {
expect 0 <= 28 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3758096384 as bv32), 28);
expect r0 == ((3758096384 as bv32) << 28 as bv6) | ((3758096384 as bv32) >> (32 - 28) as bv6);
}

// REPEAT 8 - TIME: 8.8441624 s