
method {:test} Test5() {
expect 30887 > 0 && 11584 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30887, 11584);
}

// REPEAT 6 - TIME: 26.7761231 s