
method {:test} Test9() {
expect 0 <= 2 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((536870912 as bv32), 2);
expect r0 == ((536870912 as bv32) << 2 as bv6) | ((536870912 as bv32) >> (32 - 2) as bv6);
}

// REPEAT 5 - TIME: 8.4956405 s