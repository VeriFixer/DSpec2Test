
method {:test} Test45() {
expect 10817 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10817);
expect r0 >= 0 && r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}
method {:test} Test46() {
expect 10817 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10817);
expect r0 >= 0 && r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}
method {:test} Test47() {
expect 10817 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10817);
expect r0 >= 0 && r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 24.2277696 s