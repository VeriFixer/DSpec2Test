
method {:test} Test13() {
expect 0 <= 3 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((268435456 as bv32), 3);
expect r0 == ((268435456 as bv32) << 3 as bv6) | ((268435456 as bv32) >> (32 - 3) as bv6);
}

// REPEAT 9 - TIME: 11.3580389 s