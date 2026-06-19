// dafny-synthesis_task_id_441.dfy

method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
  requires size > 0
  ensures area == 6 * size * size
{
  area := (6 + size) * size;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(1);
expect r0 == 6 * 1 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(100);
expect r0 == 6 * 100 * 100;
}

// REPEAT 1 - TIME: 5.0086603 s

method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(101);
expect r0 == 6 * 101 * 101;
}

// REPEAT 2 - TIME: 6.0292284 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(102);
expect r0 == 6 * 102 * 102;
}

// REPEAT 3 - TIME: 6.8740552 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(103);
expect r0 == 6 * 103 * 103;
}

// REPEAT 4 - TIME: 7.7102355 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(104);
expect r0 == 6 * 104 * 104;
}

// REPEAT 5 - TIME: 8.4905299 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(105);
expect r0 == 6 * 105 * 105;
}

// REPEAT 6 - TIME: 9.1708935 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(106);
expect r0 == 6 * 106 * 106;
}

// REPEAT 7 - TIME: 10.0025885 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(107);
expect r0 == 6 * 107 * 107;
}

// REPEAT 8 - TIME: 10.7921422 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(108);
expect r0 == 6 * 108 * 108;
}

// REPEAT 9 - TIME: 11.4024281 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(109);
expect r0 == 6 * 109 * 109;
}

// REPEAT 10 - TIME: 12.2390389 s
