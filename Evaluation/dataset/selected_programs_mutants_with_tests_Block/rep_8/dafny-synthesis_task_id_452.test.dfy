
method {:test} Test14() {
expect 11 >= 0 && 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(11, 11);
expect (11 > 11 ==> r0 == 11 - 11) && (11 <= 11 ==> r0 == 0);
}
method {:test} Test15() {
expect 11 >= 0 && 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(11, 10);
expect (11 > 10 ==> r0 == 11 - 10) && (11 <= 10 ==> r0 == 0);
}

// REPEAT 8 - TIME: 9.940115 s