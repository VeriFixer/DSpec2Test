
method {:test} Test22() {
expect 105 >= 0 && 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(105, 105);
expect r0 <==> 105 == 105;
}
method {:test} Test23() {
expect 106 >= 0 && 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(106, 105);
expect r0 <==> 106 == 105;
}

// REPEAT 4 - TIME: 12.9154982 s