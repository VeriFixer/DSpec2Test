
method {:test} Test39() {
expect 10815 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10815);
expect r0 >= 0 && r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}
method {:test} Test40() {
expect 10815 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10815);
expect r0 >= 0 && r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}
method {:test} Test41() {
expect 10815 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10815);
expect r0 >= 0 && r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 17.4762641 s