
method {:test} Test32() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(104);
expect r0 == fib(104);
}
method {:test} Test33() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(104);
expect r0 == fact(104);
}
method {:test} Test34() {
expect 20277 > 0 && 10138 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20277, 10138);
expect r0 == gcd(20277, 10138);
}

// REPEAT 5 - TIME: 17.3466641 s