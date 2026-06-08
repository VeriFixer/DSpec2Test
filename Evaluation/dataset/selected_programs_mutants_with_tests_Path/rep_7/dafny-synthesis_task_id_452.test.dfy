
method {:test} Test12() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(10, 9);
expect (10 > 9 ==> r0 == 10 - 9) && (10 <= 9 ==> r0 == 0);
}
method {:test} Test13() {
expect 9 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(9, 9);
expect (9 > 9 ==> r0 == 9 - 9) && (9 <= 9 ==> r0 == 0);
}

// REPEAT 7 - TIME: 13.7850814 s