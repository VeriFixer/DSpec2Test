
method {:test} Test38() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(106);
expect r0 == fib(106);
}
method {:test} Test39() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(106);
expect r0 == fact(106);
}
method {:test} Test40() {
expect 20281 > 0 && 10140 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20281, 10140);
expect r0 == gcd(20281, 10140);
}

// REPEAT 7 - TIME: 19.6796284 s