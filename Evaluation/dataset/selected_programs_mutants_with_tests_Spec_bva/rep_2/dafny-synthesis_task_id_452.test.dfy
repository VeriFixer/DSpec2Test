
method {:test} Test16() {
expect 102 >= 0 && 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(102, 102);
expect (102 > 102 ==> r0 == 102 - 102) && (102 <= 102 ==> r0 == 0);
}
method {:test} Test17() {
expect 102 >= 0 && 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(102, 101);
expect (102 > 101 ==> r0 == 102 - 101) && (102 <= 101 ==> r0 == 0);
}

// REPEAT 2 - TIME: 14.3340807 s