// dafny-synthesis_task_id_441.dfy

method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
  requires size > 0
  ensures area == 6 * size * size
{
  area := 6;
}

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(2);
expect r0 == 6 * 2 * 2;
}

// REPEAT 2 - TIME: 4.327212 s
