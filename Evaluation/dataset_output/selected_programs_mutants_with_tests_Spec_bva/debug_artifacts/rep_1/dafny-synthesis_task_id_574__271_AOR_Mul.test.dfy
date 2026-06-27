// dafny-synthesis_task_id_574.dfy

method {:testEntry} CylinderSurfaceArea(radius: real, height: real) returns (area: real)
  requires radius > 0.0 && height > 0.0
  ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
  area := 2.0 * 3.14159265358979323846 * radius * (radius * height);
}

method {:test} Test0() {
expect 1.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(1.0, 1.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0 * (1.0 + 1.0);
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(1.0/10000.0, 1.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0/10000.0 * (1.0/10000.0 + 1.0);
}
method {:test} Test2() {
expect 100.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(100.0, 1.0);
expect r0 == 2.0 * 3.14159265358979323846 * 100.0 * (100.0 + 1.0);
}
method {:test} Test3() {
expect 1.0 > 0.0 && 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(1.0, 1.0/10000.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0 * (1.0 + 1.0/10000.0);
}
method {:test} Test4() {
expect 1.0 > 0.0 && 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(1.0, 100.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0 * (1.0 + 100.0);
}

// REPEAT 1 - TIME: 5.8428415 s
