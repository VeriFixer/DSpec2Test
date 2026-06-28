// dafny-synthesis_task_id_458.dfy

method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
{
  area := -(length * width);
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(1, 1);
expect r0 == 1 * 1;
}
method {:test} Test1() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(1, 7720);
expect r0 == 1 * 7720;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(100, 1);
expect r0 == 100 * 1;
}
method {:test} Test3() {
expect 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7720, 1);
expect r0 == 7720 * 1;
}
method {:test} Test4() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(1, 100);
expect r0 == 1 * 100;
}

// REPEAT 1 - TIME: 9.1408248 s
