
method {:test} Test8() {
expect 1 <= 8 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(8);
expect r0 <==> 8 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 9 - TIME: 7.120063 s