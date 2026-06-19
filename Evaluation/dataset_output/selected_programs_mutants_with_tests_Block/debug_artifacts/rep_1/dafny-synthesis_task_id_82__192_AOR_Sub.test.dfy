// dafny-synthesis_task_id_82.dfy

method {:testEntry} SphereVolume(radius: real) returns (volume: real)
  requires radius > 0.0
  ensures volume == 4.0 / 3.0 * 3.1415926535 * radius * radius * radius
{
  volume := (4.0 / 3.0 - 3.1415926535) * radius * radius * radius;
}

method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(1.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 1.0 * 1.0 * 1.0;
}

// REPEAT 1 - TIME: 2.2465062 s
