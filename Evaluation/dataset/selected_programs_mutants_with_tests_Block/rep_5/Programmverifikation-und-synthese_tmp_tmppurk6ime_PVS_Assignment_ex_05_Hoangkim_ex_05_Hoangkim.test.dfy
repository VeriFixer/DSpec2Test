
method {:test} Test16() {
expect 8950 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8950);
expect r0 == fib(8950);
}
method {:test} Test17() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test18() {
expect 43702 > 0 && 21851 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(43702, 21851);
expect r0 == gcd(43702, 21851);
}
method {:test} Test19() {
expect 44916 > 0 && 22458 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(44916, 22458);
expect r0 == gcd(44916, 22458);
}

// REPEAT 5 - TIME: 12.9335773 s