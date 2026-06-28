// dafny-synthesis_task_id_233.dfy

method {:testEntry} CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
  requires radius > 0.0 && height > 0.0
  ensures area == 2.0 * (radius * height) * 3.14
{
  area := -(2.0 * (radius * height) * 3.14);
}

method {:test} Test0() {
expect 1.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(1.0, 1.0);
expect r0 == 2.0 * (1.0 * 1.0) * 3.14;
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(1.0/10000.0, 1.0);
expect r0 == 2.0 * (1.0/10000.0 * 1.0) * 3.14;
}
method {:test} Test2() {
expect 100.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(100.0, 1.0);
expect r0 == 2.0 * (100.0 * 1.0) * 3.14;
}
method {:test} Test3() {
expect 1.0 > 0.0 && 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(1.0, 1.0/10000.0);
expect r0 == 2.0 * (1.0 * 1.0/10000.0) * 3.14;
}
method {:test} Test4() {
expect 1.0 > 0.0 && 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(1.0, 100.0);
expect r0 == 2.0 * (1.0 * 100.0) * 3.14;
}

// REPEAT 1 - TIME: 7.8551091 s
