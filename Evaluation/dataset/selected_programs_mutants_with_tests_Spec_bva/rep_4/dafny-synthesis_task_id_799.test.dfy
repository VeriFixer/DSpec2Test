
method {:test} Test8() {
expect 0 <= 29 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3221225472 as bv32), 29);
expect r0 == ((3221225472 as bv32) << 29 as bv6) | ((3221225472 as bv32) >> (32 - 29) as bv6);
}

// REPEAT 4 - TIME: 8.1486713 s