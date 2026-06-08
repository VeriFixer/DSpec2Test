// dafny-synthesis_task_id_581.dfy

method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
  requires baseEdge > 0
  requires height > 0
  ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
  area := baseEdge * baseEdge;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 1);
expect r0 == 1 * 1 + 2 * 1 * 1;
}
method {:test} Test1() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 7720);
expect r0 == 1 * 1 + 2 * 1 * 7720;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(100, 1);
expect r0 == 100 * 100 + 2 * 100 * 1;
}
method {:test} Test4() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 100);
expect r0 == 1 * 1 + 2 * 1 * 100;
}
method {:test} Test6() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 24 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(2, 24);
expect r0 == 2 * 2 + 2 * 2 * 24;
}

// REPEAT 1 - TIME: 6.2270203 s
