
method {:test} Test10() {
expect 1 <= 4 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(4);
expect r0 <==> 4 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 4 - TIME: 12.0632824 s