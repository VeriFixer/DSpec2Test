
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
expect 20273 > 0 && 10136 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20273, 10136);
expect r0 == gcd(20273, 10136);
}

// REPEAT 3 - TIME: 7.4857504 s