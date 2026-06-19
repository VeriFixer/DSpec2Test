// dafny-synthesis_task_id_234.dfy

method {:testEntry} CubeVolume(size: int) returns (volume: int)
  requires size > 0
  ensures volume == size * size * size
{
  volume := size;
}

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(2);
expect r0 == 2 * 2 * 2;
}

// REPEAT 2 - TIME: 5.7224263 s
