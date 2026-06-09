
method {:test} Test30() {
expect 111 >= 0 && 111 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(111, 111);
expect r0 <==> 111 == 111;
}
method {:test} Test31() {
expect 112 >= 0 && 111 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(112, 111);
expect r0 <==> 112 == 111;
}

// REPEAT 8 - TIME: 14.5586608 s