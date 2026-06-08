
method {:test} Test1() {
expect 3 > 0 && 2475 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(3, 2475);
expect r0 == (3 + 2475) / 2;
}

// REPEAT 2 - TIME: 4.6149842 s