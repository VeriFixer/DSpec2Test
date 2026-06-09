
method {:test} Test1() {
expect 16678 > 0 && 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16678, 7721);
}

// REPEAT 2 - TIME: 3.4293552 s