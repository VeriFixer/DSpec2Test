
method {:test} Test16() {
expect 13 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(13, 12);
expect (13 > 12 ==> r0 == 13 - 12) && (13 <= 12 ==> r0 == 0);
}
method {:test} Test17() {
expect 12 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(12, 12);
expect (12 > 12 ==> r0 == 12 - 12) && (12 <= 12 ==> r0 == 0);
}

// REPEAT 9 - TIME: 17.284368 s