
method {:test} Test3() {
expect 0 <= 3 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3221225472 as bv32), 3);
expect r0 == ((3221225472 as bv32) << 3 as bv6) | ((3221225472 as bv32) >> (32 - 3) as bv6);
}

// REPEAT 4 - TIME: 3.6570212 s