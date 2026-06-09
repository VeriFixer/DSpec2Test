
method {:test} Test27() {
expect 1246 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1246);
expect r0 == fib(1246);
}
method {:test} Test28() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test29() {
expect 27470 > 0 && 13735 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(27470, 13735);
expect r0 == gcd(27470, 13735);
}

// REPEAT 10 - TIME: 16.5220742 s