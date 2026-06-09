
method {:test} Test26() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(102);
expect r0 == fib(102);
}
method {:test} Test27() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(102);
expect r0 == fact(102);
}
method {:test} Test28() {
expect 20273 > 0 && 10136 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20273, 10136);
expect r0 == gcd(20273, 10136);
}

// REPEAT 3 - TIME: 14.6877224 s