
method {:test} Test6() {
expect 7 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(7, 6);
expect r0 <==> 7 == 6;
}

// REPEAT 7 - TIME: 9.543861 s