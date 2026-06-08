
method {:test} Test9() {
expect 1240 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1240);
expect r0 == fib(1240);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test11() {
expect 20275 > 0 && 10137 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20275, 10137);
expect r0 == gcd(20275, 10137);
}

// REPEAT 4 - TIME: 11.0301366 s