
method {:test} Test32() {
expect 8954 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8954);
expect r0 == fib(8954);
}
method {:test} Test33() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test34() {
expect 50881 > 0 && 24222 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(50881, 24222);
expect r0 == gcd(50881, 24222);
}
method {:test} Test35() {
expect 50881 > 0 && 101226 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(50881, 101226);
expect r0 == gcd(50881, 101226);
}

// REPEAT 9 - TIME: 21.9025668 s