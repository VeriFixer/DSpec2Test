
method {:test} Test35() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(105);
expect r0 == fib(105);
}
method {:test} Test36() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(105);
expect r0 == fact(105);
}
method {:test} Test37() {
expect 20279 > 0 && 10139 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20279, 10139);
expect r0 == gcd(20279, 10139);
}

// REPEAT 6 - TIME: 18.5476116 s