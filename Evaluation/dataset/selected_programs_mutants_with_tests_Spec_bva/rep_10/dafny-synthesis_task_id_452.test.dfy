
method {:test} Test32() {
expect 114 >= 0 && 114 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(114, 114);
expect (114 > 114 ==> r0 == 114 - 114) && (114 <= 114 ==> r0 == 0);
}
method {:test} Test33() {
expect 114 >= 0 && 113 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(114, 113);
expect (114 > 113 ==> r0 == 114 - 113) && (114 <= 113 ==> r0 == 0);
}

// REPEAT 10 - TIME: 26.5110756 s