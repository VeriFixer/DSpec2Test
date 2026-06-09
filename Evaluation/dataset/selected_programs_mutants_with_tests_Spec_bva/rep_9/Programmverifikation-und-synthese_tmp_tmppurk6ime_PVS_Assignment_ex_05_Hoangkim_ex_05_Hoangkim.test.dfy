
method {:test} Test44() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(108);
expect r0 == fib(108);
}
method {:test} Test45() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(108);
expect r0 == fact(108);
}
method {:test} Test46() {
expect 23876 > 0 && 11938 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23876, 11938);
expect r0 == gcd(23876, 11938);
}

// REPEAT 9 - TIME: 22.1316648 s