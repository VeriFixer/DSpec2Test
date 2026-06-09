
method {:test} Test32() {
expect 113 >= 0 && 113 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(113, 113);
expect r0 <==> 113 == 113;
}
method {:test} Test33() {
expect 113 >= 0 && 112 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(113, 112);
expect r0 <==> 113 == 112;
}

// REPEAT 9 - TIME: 15.1712408 s