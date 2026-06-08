
method {:test} Test12() {
expect 8949 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8949);
expect r0 == fib(8949);
}
method {:test} Test13() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test14() {
expect 42630 > 0 && 18389 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42630, 18389);
expect r0 == gcd(42630, 18389);
}

// REPEAT 4 - TIME: 11.5120607 s