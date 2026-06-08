
method {:test} Test24() {
expect 107 >= 0 && 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(107, 107);
expect r0 <==> 107 == 107;
}
method {:test} Test25() {
expect 107 >= 0 && 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(107, 106);
expect r0 <==> 107 == 106;
}

// REPEAT 5 - TIME: 13.7247002 s