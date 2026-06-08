
method {:test} Test3() {
expect 4 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(4, 3);
expect r0 <==> 4 == 3;
}

// REPEAT 4 - TIME: 6.6456137 s