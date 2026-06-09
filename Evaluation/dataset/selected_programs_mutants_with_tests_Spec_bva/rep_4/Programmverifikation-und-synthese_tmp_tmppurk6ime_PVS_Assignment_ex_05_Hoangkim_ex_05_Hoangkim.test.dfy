
method {:test} Test29() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(103);
expect r0 == fib(103);
}
method {:test} Test30() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(103);
expect r0 == fact(103);
}
method {:test} Test31() {
expect 20275 > 0 && 10137 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20275, 10137);
expect r0 == gcd(20275, 10137);
}

// REPEAT 4 - TIME: 15.9629112 s