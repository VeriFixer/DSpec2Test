
method {:test} Test36() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10);
expect r0 >= 0 && r0 * r0 <= 10 < (r0 + 1) * (r0 + 1);
}
method {:test} Test37() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(11);
expect r0 >= 0 && r0 * r0 <= 11 < (r0 + 1) * (r0 + 1);
}
method {:test} Test38() {
expect 899 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(899);
expect r0 >= 0 && r0 * r0 <= 899 < (r0 + 1) * (r0 + 1);
}
method {:test} Test39() {
expect 1599 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(1599);
expect r0 >= 0 && r0 * r0 <= 1599 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 18.1788565 s