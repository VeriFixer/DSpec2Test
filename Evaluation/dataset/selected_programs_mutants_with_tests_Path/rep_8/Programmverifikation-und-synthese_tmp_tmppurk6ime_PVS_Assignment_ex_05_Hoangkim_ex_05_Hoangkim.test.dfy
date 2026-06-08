
method {:test} Test21() {
expect 543 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(543);
expect r0 == fib(543);
}
method {:test} Test22() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test23() {
expect 7951 > 0 && 23622 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7951, 23622);
expect r0 == gcd(7951, 23622);
}

// REPEAT 8 - TIME: 82.3269245 s