
method {:test} Test32() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}
method {:test} Test33() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10);
expect r0 >= 0 && r0 * r0 <= 10 < (r0 + 1) * (r0 + 1);
}
method {:test} Test34() {
expect 840 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(840);
expect r0 >= 0 && r0 * r0 <= 840 < (r0 + 1) * (r0 + 1);
}
method {:test} Test35() {
expect 841 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(841);
expect r0 >= 0 && r0 * r0 <= 841 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 16.6780019 s