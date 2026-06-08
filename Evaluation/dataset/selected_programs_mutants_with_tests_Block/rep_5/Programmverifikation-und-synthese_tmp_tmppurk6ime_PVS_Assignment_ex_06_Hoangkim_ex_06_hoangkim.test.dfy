
method {:test} Test8() {
expect 40880 > 0 && 20440 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40880, 20440);
}
method {:test} Test9() {
expect 42117 > 0 && 20440 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42117, 20440);
}

// REPEAT 5 - TIME: 8.0282561 s