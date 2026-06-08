
method {:test} Test30() {
expect 112 >= 0 && 112 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(112, 112);
expect (112 > 112 ==> r0 == 112 - 112) && (112 <= 112 ==> r0 == 0);
}
method {:test} Test31() {
expect 113 >= 0 && 112 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(113, 112);
expect (113 > 112 ==> r0 == 113 - 112) && (113 <= 112 ==> r0 == 0);
}

// REPEAT 9 - TIME: 25.2110492 s