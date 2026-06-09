
method {:test} Test7() {
expect 1 <= 7 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(7);
expect r0 <==> 7 == 4 || 7 == 6 || 7 == 9 || 7 == 11;
}
method {:test} Test8() {
expect 1 <= 11 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(11);
expect r0 <==> 11 == 4 || 11 == 6 || 11 == 9 || 11 == 11;
}

// REPEAT 3 - TIME: 6.7064501 s