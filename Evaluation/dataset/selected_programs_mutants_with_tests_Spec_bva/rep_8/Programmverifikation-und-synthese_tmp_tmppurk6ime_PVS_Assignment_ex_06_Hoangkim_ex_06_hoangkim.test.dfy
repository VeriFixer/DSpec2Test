
method {:test} Test16() {
expect 16843 > 0 && 8421 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16843, 8421);
}

// REPEAT 8 - TIME: 15.3024039 s