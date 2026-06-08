
method {:test} Test41() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(107);
expect r0 == fib(107);
}
method {:test} Test42() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(107);
expect r0 == fact(107);
}
method {:test} Test43() {
expect 23874 > 0 && 11937 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23874, 11937);
expect r0 == gcd(23874, 11937);
}

// REPEAT 8 - TIME: 24.7432551 s