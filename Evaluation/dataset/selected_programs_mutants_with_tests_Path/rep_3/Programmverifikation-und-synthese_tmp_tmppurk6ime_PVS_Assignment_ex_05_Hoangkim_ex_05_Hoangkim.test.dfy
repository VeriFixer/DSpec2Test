
method {:test} Test6() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(3);
expect r0 == fib(3);
}
method {:test} Test7() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(4);
expect r0 == fact(4);
}
method {:test} Test8() {
expect 3 > 0 && 454 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(3, 454);
expect r0 == gcd(3, 454);
}

// REPEAT 3 - TIME: 37.9130237 s