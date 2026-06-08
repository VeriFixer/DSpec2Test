
method {:test} Test18() {
expect 542 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(542);
expect r0 == fib(542);
}
method {:test} Test19() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test20() {
expect 7950 > 0 && 15900 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7950, 15900);
expect r0 == gcd(7950, 15900);
}

// REPEAT 7 - TIME: 71.1337348 s