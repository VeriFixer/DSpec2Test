
method {:test} Test4() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(2);
expect r0 == fib(2);
}
method {:test} Test5() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(3);
expect r0 == fact(3);
}
method {:test} Test6() {
expect 38011 > 0 && 18387 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(38011, 18387);
expect r0 == gcd(38011, 18387);
}
method {:test} Test7() {
expect 42628 > 0 && 18387 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42628, 18387);
expect r0 == gcd(42628, 18387);
}

// REPEAT 2 - TIME: 7.0289673 s