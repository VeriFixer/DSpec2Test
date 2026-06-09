
method {:test} Test24() {
expect 8952 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8952);
expect r0 == fib(8952);
}
method {:test} Test25() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test26() {
expect 46156 > 0 && 22460 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46156, 22460);
expect r0 == gcd(46156, 22460);
}
method {:test} Test27() {
expect 48440 > 0 && 24220 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(48440, 24220);
expect r0 == gcd(48440, 24220);
}

// REPEAT 7 - TIME: 16.42913 s