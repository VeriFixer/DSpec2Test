
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
expect 20270 > 0 && 10135 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20270, 10135);
expect r0 == gcd(20270, 10135);
}

// REPEAT 2 - TIME: 5.8226461 s