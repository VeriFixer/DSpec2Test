
method {:test} Test12() {
expect 1241 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1241);
expect r0 == fib(1241);
}
method {:test} Test13() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test14() {
expect 23868 > 0 && 11934 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23868, 11934);
expect r0 == gcd(23868, 11934);
}

// REPEAT 5 - TIME: 12.6361543 s