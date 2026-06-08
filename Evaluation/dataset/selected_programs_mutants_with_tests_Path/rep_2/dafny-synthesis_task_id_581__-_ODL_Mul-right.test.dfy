// dafny-synthesis_task_id_581.dfy

method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
  requires baseEdge > 0
  requires height > 0
  ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
  area := baseEdge + 2;
}

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(2, 2);
expect r0 == 2 * 2 + 2 * 2 * 2;
}

// REPEAT 2 - TIME: 4.4315791 s
