
method {:test} Test5() {
expect 16836 > 0 && 8418 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16836, 8418);
}

// REPEAT 6 - TIME: 8.8753183 s