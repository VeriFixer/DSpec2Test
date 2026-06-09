
method {:test} Test9() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(10, 9);
expect r0 <==> 10 == 9;
}

// REPEAT 10 - TIME: 11.8027235 s