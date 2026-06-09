
method {:test} Test28() {
expect 110 >= 0 && 110 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(110, 110);
expect r0 <==> 110 == 110;
}
method {:test} Test29() {
expect 110 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(110, 109);
expect r0 <==> 110 == 109;
}

// REPEAT 7 - TIME: 13.8228177 s