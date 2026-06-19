// dafny-synthesis_task_id_581.dfy

method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
  requires baseEdge > 0
  requires height > 0
  ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
  area := baseEdge * baseEdge + (2 * baseEdge - height);
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 1);
expect r0 == 1 * 1 + 2 * 1 * 1;
}

// REPEAT 1 - TIME: 2.385604 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(2, 2);
expect r0 == 2 * 2 + 2 * 2 * 2;
}

// REPEAT 2 - TIME: 3.1799645 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(3, 3);
expect r0 == 3 * 3 + 2 * 3 * 3;
}

// REPEAT 3 - TIME: 4.0162189 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(4, 4);
expect r0 == 4 * 4 + 2 * 4 * 4;
}

// REPEAT 4 - TIME: 4.9867454 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(5, 5);
expect r0 == 5 * 5 + 2 * 5 * 5;
}

// REPEAT 5 - TIME: 5.7720415 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(6, 6);
expect r0 == 6 * 6 + 2 * 6 * 6;
}

// REPEAT 6 - TIME: 6.5991857 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(7, 7);
expect r0 == 7 * 7 + 2 * 7 * 7;
}

// REPEAT 7 - TIME: 7.3387403 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(8, 8);
expect r0 == 8 * 8 + 2 * 8 * 8;
}

// REPEAT 8 - TIME: 8.1011801 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(9, 9);
expect r0 == 9 * 9 + 2 * 9 * 9;
}

// REPEAT 9 - TIME: 8.8899038 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(10, 10);
expect r0 == 10 * 10 + 2 * 10 * 10;
}

// REPEAT 10 - TIME: 9.5108928 s
