
method {:test} Test20() {
expect 8951 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8951);
expect r0 == fib(8951);
}
method {:test} Test21() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test22() {
expect 46155 > 0 && 22459 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46155, 22459);
expect r0 == gcd(46155, 22459);
}

// REPEAT 6 - TIME: 14.7401297 s