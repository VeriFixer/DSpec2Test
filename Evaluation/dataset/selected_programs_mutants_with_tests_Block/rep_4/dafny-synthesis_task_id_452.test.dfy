
method {:test} Test6() {
expect 5 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(5, 5);
expect (5 > 5 ==> r0 == 5 - 5) && (5 <= 5 ==> r0 == 0);
}
method {:test} Test7() {
expect 5 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(5, 4);
expect (5 > 4 ==> r0 == 5 - 4) && (5 <= 4 ==> r0 == 0);
}

// REPEAT 4 - TIME: 5.5410022 s