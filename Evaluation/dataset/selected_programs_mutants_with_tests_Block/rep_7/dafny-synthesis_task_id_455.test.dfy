
method {:test} Test6() {
expect 1 <= 10 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(10);
expect r0 <==> 10 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 7 - TIME: 6.0783403 s