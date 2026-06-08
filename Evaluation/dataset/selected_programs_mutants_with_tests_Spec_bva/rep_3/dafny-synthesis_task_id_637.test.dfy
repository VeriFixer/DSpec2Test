
method {:test} Test20() {
expect 104 >= 0 && 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(104, 104);
expect r0 <==> 104 == 104;
}
method {:test} Test21() {
expect 104 >= 0 && 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(104, 103);
expect r0 <==> 104 == 103;
}

// REPEAT 3 - TIME: 12.0383709 s