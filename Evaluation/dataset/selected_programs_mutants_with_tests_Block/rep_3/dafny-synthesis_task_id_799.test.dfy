
method {:test} Test2() {
expect 0 <= 2 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1073741824 as bv32), 2);
expect r0 == ((1073741824 as bv32) << 2 as bv6) | ((1073741824 as bv32) >> (32 - 2) as bv6);
}

// REPEAT 3 - TIME: 3.5139559 s