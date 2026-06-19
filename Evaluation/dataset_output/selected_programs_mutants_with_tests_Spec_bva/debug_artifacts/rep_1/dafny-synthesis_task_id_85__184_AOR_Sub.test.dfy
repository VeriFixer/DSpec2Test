// dafny-synthesis_task_id_85.dfy

method {:testEntry} SphereSurfaceArea(radius: real) returns (area: real)
  requires radius > 0.0
  ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
  area := (4.0 - 3.14159265358979323846) * radius * radius;
}

method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(1.0);
expect r0 == 4.0 * 3.14159265358979323846 * 1.0 * 1.0;
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(1.0/10000.0);
expect r0 == 4.0 * 3.14159265358979323846 * 1.0/10000.0 * 1.0/10000.0;
}
method {:test} Test2() {
expect 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(100.0);
expect r0 == 4.0 * 3.14159265358979323846 * 100.0 * 100.0;
}

// REPEAT 1 - TIME: 5.0818175 s
