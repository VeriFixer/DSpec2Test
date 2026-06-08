
method {:test} Test10() {
expect 42118 > 0 && 20441 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42118, 20441);
}
method {:test} Test11() {
expect 57556 > 0 && 28778 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(57556, 28778);
}

// REPEAT 6 - TIME: 9.1443477 s