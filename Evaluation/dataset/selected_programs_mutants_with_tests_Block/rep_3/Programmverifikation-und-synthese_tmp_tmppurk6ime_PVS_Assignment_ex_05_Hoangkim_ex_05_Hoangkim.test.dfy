
method {:test} Test8() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(3);
expect r0 == fib(3);
}
method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(4);
expect r0 == fact(4);
}
method {:test} Test10() {
expect 42629 > 0 && 18388 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42629, 18388);
expect r0 == gcd(42629, 18388);
}

// REPEAT 3 - TIME: 9.1353656 s