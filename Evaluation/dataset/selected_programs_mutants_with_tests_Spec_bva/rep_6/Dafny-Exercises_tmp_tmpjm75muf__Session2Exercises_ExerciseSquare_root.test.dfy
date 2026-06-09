
method {:test} Test36() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}
method {:test} Test37() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}
method {:test} Test38() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 16.497592 s