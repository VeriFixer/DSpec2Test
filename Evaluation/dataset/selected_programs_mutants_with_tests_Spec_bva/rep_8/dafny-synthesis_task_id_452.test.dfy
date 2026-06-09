
method {:test} Test28() {
expect 111 >= 0 && 111 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(111, 111);
expect (111 > 111 ==> r0 == 111 - 111) && (111 <= 111 ==> r0 == 0);
}
method {:test} Test29() {
expect 111 >= 0 && 110 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(111, 110);
expect (111 > 110 ==> r0 == 111 - 110) && (111 <= 110 ==> r0 == 0);
}

// REPEAT 8 - TIME: 22.1340465 s