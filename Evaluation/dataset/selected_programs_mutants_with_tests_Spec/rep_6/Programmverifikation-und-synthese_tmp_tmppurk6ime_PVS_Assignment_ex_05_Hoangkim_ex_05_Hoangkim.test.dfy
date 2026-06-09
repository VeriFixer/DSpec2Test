
method {:test} Test15() {
expect 1242 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1242);
expect r0 == fib(1242);
}
method {:test} Test16() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test17() {
expect 23870 > 0 && 11935 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23870, 11935);
expect r0 == gcd(23870, 11935);
}

// REPEAT 6 - TIME: 11.6305952 s