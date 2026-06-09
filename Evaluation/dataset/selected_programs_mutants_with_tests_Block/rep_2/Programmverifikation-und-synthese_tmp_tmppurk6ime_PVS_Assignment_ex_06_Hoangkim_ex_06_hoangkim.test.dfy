
method {:test} Test2() {
expect 25436 > 0 && 8858 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(25436, 8858);
}
method {:test} Test3() {
expect 17716 > 0 && 8858 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17716, 8858);
}

// REPEAT 2 - TIME: 3.8818179 s