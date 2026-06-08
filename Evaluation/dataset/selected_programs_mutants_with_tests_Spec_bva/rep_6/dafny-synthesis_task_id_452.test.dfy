
method {:test} Test24() {
expect 108 >= 0 && 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(108, 108);
expect (108 > 108 ==> r0 == 108 - 108) && (108 <= 108 ==> r0 == 0);
}
method {:test} Test25() {
expect 108 >= 0 && 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(108, 107);
expect (108 > 107 ==> r0 == 108 - 107) && (108 <= 107 ==> r0 == 0);
}

// REPEAT 6 - TIME: 21.0695137 s