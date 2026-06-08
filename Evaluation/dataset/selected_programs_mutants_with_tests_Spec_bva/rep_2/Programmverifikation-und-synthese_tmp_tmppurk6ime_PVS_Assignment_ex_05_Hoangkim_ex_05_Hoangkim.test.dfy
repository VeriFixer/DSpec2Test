
method {:test} Test23() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(101);
expect r0 == fib(101);
}
method {:test} Test24() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(101);
expect r0 == fact(101);
}
method {:test} Test25() {
expect 20270 > 0 && 10135 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20270, 10135);
expect r0 == gcd(20270, 10135);
}

// REPEAT 2 - TIME: 15.9929378 s