
method {:test} Test9() {
expect 1 <= 5 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(5);
expect r0 <==> 5 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 10 - TIME: 5.2183294 s