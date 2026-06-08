
method {:test} Test24() {
expect 1245 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1245);
expect r0 == fib(1245);
}
method {:test} Test25() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test26() {
expect 23877 > 0 && 11938 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23877, 11938);
expect r0 == gcd(23877, 11938);
}

// REPEAT 9 - TIME: 19.0015739 s