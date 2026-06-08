
method {:test} Test18() {
expect 1243 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1243);
expect r0 == fib(1243);
}
method {:test} Test19() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test20() {
expect 23873 > 0 && 11936 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23873, 11936);
expect r0 == gcd(23873, 11936);
}

// REPEAT 7 - TIME: 15.803472 s