
method {:test} Test3() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(2);
expect r0 == fib(2);
}
method {:test} Test4() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(3);
expect r0 == fact(3);
}
method {:test} Test5() {
expect 2 > 0 && 453 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(2, 453);
expect r0 == gcd(2, 453);
}

// REPEAT 2 - TIME: 22.2493235 s