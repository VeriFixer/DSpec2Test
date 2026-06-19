// dafny-synthesis_task_id_458.dfy

method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
{
  area := length * length;
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

// REPEAT 1 - TIME: 6.5165562 s

method {:test} Test9() {
expect 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7721, 7721);
expect r0 == 7721 * 7721;
}

// REPEAT 2 - TIME: 7.4614573 s

method {:test} Test10() {
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7722, 7722);
expect r0 == 7722 * 7722;
}

// REPEAT 3 - TIME: 8.4230855 s

method {:test} Test11() {
expect 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7723, 7723);
expect r0 == 7723 * 7723;
}

// REPEAT 4 - TIME: 9.2756429 s

method {:test} Test12() {
expect 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7724, 7724);
expect r0 == 7724 * 7724;
}

// REPEAT 5 - TIME: 10.0327068 s

method {:test} Test13() {
expect 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7725, 7725);
expect r0 == 7725 * 7725;
}

// REPEAT 6 - TIME: 10.800689 s

method {:test} Test14() {
expect 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7726, 7726);
expect r0 == 7726 * 7726;
}

// REPEAT 7 - TIME: 11.5269092 s

method {:test} Test15() {
expect 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7727, 7727);
expect r0 == 7727 * 7727;
}

// REPEAT 8 - TIME: 12.2650299 s

method {:test} Test16() {
expect 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7728, 7728);
expect r0 == 7728 * 7728;
}

// REPEAT 9 - TIME: 13.0245423 s

method {:test} Test17() {
expect 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7729, 7729);
expect r0 == 7729 * 7729;
}

// REPEAT 10 - TIME: 13.7071655 s
