
method {:test} Test42() {
expect 10816 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10816);
expect r0 >= 0 && r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}
method {:test} Test43() {
expect 10816 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10816);
expect r0 >= 0 && r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}
method {:test} Test44() {
expect 10816 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10816);
expect r0 >= 0 && r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 22.7547255 s