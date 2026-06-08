
method {:test} Test8() {
expect 6 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(6, 6);
expect (6 > 6 ==> r0 == 6 - 6) && (6 <= 6 ==> r0 == 0);
}
method {:test} Test9() {
expect 7 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(7, 6);
expect (7 > 6 ==> r0 == 7 - 6) && (7 <= 6 ==> r0 == 0);
}

// REPEAT 5 - TIME: 10.8750844 s