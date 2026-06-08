
method {:test} Test29() {
expect 1 <= 8 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(8);
expect r0 <==> 8 == 4 || 8 == 6 || 8 == 9 || 8 == 11;
}

// REPEAT 4 - TIME: 18.3050396 s