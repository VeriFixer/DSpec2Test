
method {:test} Test12() {
expect 540 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(540);
expect r0 == fib(540);
}
method {:test} Test13() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test14() {
expect 7948 > 0 && 15896 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7948, 15896);
expect r0 == gcd(7948, 15896);
}

// REPEAT 5 - TIME: 60.182203 s