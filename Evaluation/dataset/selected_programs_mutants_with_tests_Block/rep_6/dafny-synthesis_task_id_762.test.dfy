
method {:test} Test19() {
expect 1 <= 1 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(1);
expect r0 <==> 1 == 4 || 1 == 6 || 1 == 9 || 1 == 11;
}

// REPEAT 6 - TIME: 11.1559247 s