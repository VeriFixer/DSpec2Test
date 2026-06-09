
method {:test} Test15() {
expect 541 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(541);
expect r0 == fib(541);
}
method {:test} Test16() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test17() {
expect 7949 > 0 && 15898 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7949, 15898);
expect r0 == gcd(7949, 15898);
}

// REPEAT 6 - TIME: 71.1628209 s