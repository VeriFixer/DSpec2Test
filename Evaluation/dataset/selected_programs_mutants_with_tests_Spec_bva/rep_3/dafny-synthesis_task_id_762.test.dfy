
method {:test} Test28() {
expect 1 <= 7 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(7);
expect r0 <==> 7 == 4 || 7 == 6 || 7 == 9 || 7 == 11;
}

// REPEAT 3 - TIME: 16.8904629 s