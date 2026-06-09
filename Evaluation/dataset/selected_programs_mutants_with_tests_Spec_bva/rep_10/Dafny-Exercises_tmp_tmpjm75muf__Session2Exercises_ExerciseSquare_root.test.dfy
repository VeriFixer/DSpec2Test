
method {:test} Test48() {
expect 10818 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10818);
expect r0 >= 0 && r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}
method {:test} Test49() {
expect 10818 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10818);
expect r0 >= 0 && r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}
method {:test} Test50() {
expect 10818 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10818);
expect r0 >= 0 && r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 20.5284254 s