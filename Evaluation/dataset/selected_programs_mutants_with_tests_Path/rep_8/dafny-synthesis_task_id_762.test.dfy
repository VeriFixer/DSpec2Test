
method {:test} Test10() {
expect 1 <= 11 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(11);
expect r0 <==> 11 == 4 || 11 == 6 || 11 == 9 || 11 == 11;
}

// REPEAT 8 - TIME: 33.9608122 s