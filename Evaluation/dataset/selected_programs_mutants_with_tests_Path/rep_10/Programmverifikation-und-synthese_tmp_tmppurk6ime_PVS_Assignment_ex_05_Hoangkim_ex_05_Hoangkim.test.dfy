
method {:test} Test27() {
expect 545 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(545);
expect r0 == fib(545);
}
method {:test} Test28() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test29() {
expect 19531 > 0 && 39062 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(19531, 39062);
expect r0 == gcd(19531, 39062);
}

// REPEAT 10 - TIME: 109.4791004 s