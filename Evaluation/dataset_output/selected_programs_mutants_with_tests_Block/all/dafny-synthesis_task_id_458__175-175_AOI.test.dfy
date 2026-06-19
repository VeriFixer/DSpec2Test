// dafny-synthesis_task_id_458.dfy

method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
{
  area := -length * width;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 1 - TIME: 2.1880727 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(2, 2);
expect r0 == 2 * 2;
}

// REPEAT 2 - TIME: 3.0036117 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 3.8768951 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(4, 4);
expect r0 == 4 * 4;
}

// REPEAT 4 - TIME: 4.6203767 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(5, 5);
expect r0 == 5 * 5;
}

// REPEAT 5 - TIME: 5.2647804 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(6, 6);
expect r0 == 6 * 6;
}

// REPEAT 6 - TIME: 5.9180377 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 7 - TIME: 6.641093 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(8, 8);
expect r0 == 8 * 8;
}

// REPEAT 8 - TIME: 7.2082336 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(9, 9);
expect r0 == 9 * 9;
}

// REPEAT 9 - TIME: 7.7938975 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(10, 10);
expect r0 == 10 * 10;
}

// REPEAT 10 - TIME: 8.358866 s
