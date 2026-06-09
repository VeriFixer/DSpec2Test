
method {:test} Test27() {
expect 1 <= 3 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(3);
expect r0 <==> 3 == 4 || 3 == 6 || 3 == 9 || 3 == 11;
}

// REPEAT 8 - TIME: 13.4067623 s