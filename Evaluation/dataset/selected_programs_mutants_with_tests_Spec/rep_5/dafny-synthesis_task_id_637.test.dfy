
method {:test} Test8() {
expect 6 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(6, 6);
expect r0 <==> 6 == 6;
}
method {:test} Test9() {
expect 7 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(7, 6);
expect r0 <==> 7 == 6;
}

// REPEAT 5 - TIME: 8.3854219 s