// dafny-synthesis_task_id_441.dfy

method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
  requires size > 0
  ensures area == 6 * size * size
{
  area := 6 * size + size;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(1);
expect r0 == 6 * 1 * 1;
}

// REPEAT 1 - TIME: 3.223038 s
