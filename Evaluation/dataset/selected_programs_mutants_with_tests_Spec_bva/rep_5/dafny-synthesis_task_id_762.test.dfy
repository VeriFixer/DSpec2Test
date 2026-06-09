
method {:test} Test30() {
expect 1 <= 5 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(5);
expect r0 <==> 5 == 4 || 5 == 6 || 5 == 9 || 5 == 11;
}

// REPEAT 5 - TIME: 17.4775644 s