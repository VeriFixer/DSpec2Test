
method {:test} Test10() {
expect 8 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(8, 7);
expect (8 > 7 ==> r0 == 8 - 7) && (8 <= 7 ==> r0 == 0);
}
method {:test} Test11() {
expect 8 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(8, 8);
expect (8 > 8 ==> r0 == 8 - 8) && (8 <= 8 ==> r0 == 0);
}

// REPEAT 6 - TIME: 12.5951987 s