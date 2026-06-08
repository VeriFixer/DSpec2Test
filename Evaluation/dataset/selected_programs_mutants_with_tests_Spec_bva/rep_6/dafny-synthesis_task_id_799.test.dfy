
method {:test} Test10() {
expect 0 <= 28 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2684354560 as bv32), 28);
expect r0 == ((2684354560 as bv32) << 28 as bv6) | ((2684354560 as bv32) >> (32 - 28) as bv6);
}

// REPEAT 6 - TIME: 9.5017673 s