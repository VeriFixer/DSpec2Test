
method {:test} Test28() {
expect 8953 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8953);
expect r0 == fib(8953);
}
method {:test} Test29() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test30() {
expect 48442 > 0 && 24221 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(48442, 24221);
expect r0 == gcd(48442, 24221);
}
method {:test} Test31() {
expect 50880 > 0 && 24221 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(50880, 24221);
expect r0 == gcd(50880, 24221);
}

// REPEAT 8 - TIME: 18.1036811 s