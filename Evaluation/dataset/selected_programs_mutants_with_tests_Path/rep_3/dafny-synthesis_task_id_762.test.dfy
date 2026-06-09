
method {:test} Test5() {
expect 1 <= 7 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(7);
expect r0 <==> 7 == 4 || 7 == 6 || 7 == 9 || 7 == 11;
}

// REPEAT 3 - TIME: 14.3060475 s