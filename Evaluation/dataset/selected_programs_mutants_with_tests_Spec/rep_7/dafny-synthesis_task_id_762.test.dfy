
method {:test} Test10() {
expect 1 <= 2 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(2);
expect r0 <==> 2 == 4 || 2 == 6 || 2 == 9 || 2 == 11;
}

// REPEAT 7 - TIME: 15.2734096 s