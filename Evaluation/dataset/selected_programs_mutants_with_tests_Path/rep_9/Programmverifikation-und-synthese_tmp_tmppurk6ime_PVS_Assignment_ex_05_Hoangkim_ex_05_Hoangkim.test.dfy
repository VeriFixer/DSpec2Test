
method {:test} Test24() {
expect 544 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(544);
expect r0 == fib(544);
}
method {:test} Test25() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test26() {
expect 7952 > 0 && 23623 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7952, 23623);
expect r0 == gcd(7952, 23623);
}

// REPEAT 9 - TIME: 106.4605983 s