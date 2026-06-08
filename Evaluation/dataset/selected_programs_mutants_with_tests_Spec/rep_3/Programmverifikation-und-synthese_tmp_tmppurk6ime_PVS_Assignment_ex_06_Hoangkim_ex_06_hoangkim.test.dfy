
method {:test} Test2() {
expect 16679 > 0 && 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16679, 7722);
}

// REPEAT 3 - TIME: 5.9671052 s