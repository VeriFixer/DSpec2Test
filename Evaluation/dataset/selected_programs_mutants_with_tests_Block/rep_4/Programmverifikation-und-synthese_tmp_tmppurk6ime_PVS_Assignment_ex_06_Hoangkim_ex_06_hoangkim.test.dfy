
method {:test} Test6() {
expect 40878 > 0 && 20439 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40878, 20439);
}

// REPEAT 4 - TIME: 6.3656278 s