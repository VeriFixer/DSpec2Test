
method {:test} Test4() {
expect 3 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(3, 3);
expect (3 > 3 ==> r0 == 3 - 3) && (3 <= 3 ==> r0 == 0);
}
method {:test} Test5() {
expect 4 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(4, 3);
expect (4 > 3 ==> r0 == 4 - 3) && (4 <= 3 ==> r0 == 0);
}

// REPEAT 3 - TIME: 4.8303502 s