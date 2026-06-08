
method {:test} Test9() {
expect 46330 > 0 && 23165 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46330, 23165);
}

// REPEAT 10 - TIME: 37.5945564 s