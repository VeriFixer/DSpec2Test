
method {:test} Test14() {
expect 0 <= 25 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2415919104 as bv32), 25);
expect r0 == ((2415919104 as bv32) << 25 as bv6) | ((2415919104 as bv32) >> (32 - 25) as bv6);
}

// REPEAT 10 - TIME: 11.4906062 s