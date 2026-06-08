
method {:test} Test40() {
expect 1 <= 9 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(9);
expect r0 <==> 9 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 2 - TIME: 21.8321254 s