
method {:test} Test47() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(109);
expect r0 == fib(109);
}
method {:test} Test48() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(109);
expect r0 == fact(109);
}
method {:test} Test49() {
expect 23879 > 0 && 11939 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23879, 11939);
expect r0 == gcd(23879, 11939);
}

// REPEAT 10 - TIME: 28.0921713 s