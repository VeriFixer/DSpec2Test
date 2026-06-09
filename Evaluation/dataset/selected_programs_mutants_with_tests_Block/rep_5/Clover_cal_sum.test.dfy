
method {:test} Test4() {
expect 1801 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1801);
expect r0 == 1801 * (1801 + 1) / 2;
}

// REPEAT 5 - TIME: 4.3423225 s