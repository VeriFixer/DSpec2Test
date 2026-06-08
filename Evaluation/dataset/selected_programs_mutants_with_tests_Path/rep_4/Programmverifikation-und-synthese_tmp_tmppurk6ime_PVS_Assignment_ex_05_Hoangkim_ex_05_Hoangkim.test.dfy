
method {:test} Test9() {
expect 539 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(539);
expect r0 == fib(539);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test11() {
expect 7947 > 0 && 15894 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7947, 15894);
expect r0 == gcd(7947, 15894);
}

// REPEAT 4 - TIME: 41.2176702 s