
method {:test} Test26() {
expect 109 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(109, 109);
expect (109 > 109 ==> r0 == 109 - 109) && (109 <= 109 ==> r0 == 0);
}
method {:test} Test27() {
expect 110 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(110, 109);
expect (110 > 109 ==> r0 == 110 - 109) && (110 <= 109 ==> r0 == 0);
}

// REPEAT 7 - TIME: 20.8398373 s