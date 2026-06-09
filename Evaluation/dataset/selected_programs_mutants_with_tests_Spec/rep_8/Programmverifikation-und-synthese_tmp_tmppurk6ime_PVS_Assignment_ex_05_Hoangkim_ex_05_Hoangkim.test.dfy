
method {:test} Test21() {
expect 1244 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1244);
expect r0 == fib(1244);
}
method {:test} Test22() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test23() {
expect 23875 > 0 && 11937 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23875, 11937);
expect r0 == gcd(23875, 11937);
}

// REPEAT 8 - TIME: 14.1564218 s