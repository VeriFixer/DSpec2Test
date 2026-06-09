
method {:test} Test5() {
expect 6 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(6, 5);
expect r0 <==> 6 == 5;
}

// REPEAT 6 - TIME: 8.7147132 s