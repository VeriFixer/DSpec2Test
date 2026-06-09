
method {:test} Test4() {
expect 1 <= 10 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(10);
expect r0 <==> 10 == 4 || 10 == 6 || 10 == 9 || 10 == 11;
}

// REPEAT 2 - TIME: 10.9564398 s