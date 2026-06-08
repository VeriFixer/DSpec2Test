
method {:test} Test36() {
expect 8955 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8955);
expect r0 == fib(8955);
}
method {:test} Test37() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test38() {
expect 217892 > 0 && 108946 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(217892, 108946);
expect r0 == gcd(217892, 108946);
}
method {:test} Test39() {
expect 202454 > 0 && 101227 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(202454, 101227);
expect r0 == gcd(202454, 101227);
}

// REPEAT 10 - TIME: 23.9417986 s