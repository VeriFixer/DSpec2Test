// dafny-synthesis_task_id_581.dfy

method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
  requires baseEdge > 0
  requires height > 0
  ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
  area := 2 * baseEdge * height;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 1);
expect r0 == 1 * 1 + 2 * 1 * 1;
}

// REPEAT 1 - TIME: 2.1499369 s
