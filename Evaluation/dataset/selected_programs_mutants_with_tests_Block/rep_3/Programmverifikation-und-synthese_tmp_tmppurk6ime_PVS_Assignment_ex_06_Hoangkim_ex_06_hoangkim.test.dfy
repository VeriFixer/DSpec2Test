
method {:test} Test4() {
expect 40876 > 0 && 20438 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40876, 20438);
}
method {:test} Test5() {
expect 25437 > 0 && 8859 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(25437, 8859);
}

// REPEAT 3 - TIME: 5.3590757 s