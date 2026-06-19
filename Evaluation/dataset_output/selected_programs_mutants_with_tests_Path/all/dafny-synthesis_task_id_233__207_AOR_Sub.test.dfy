// dafny-synthesis_task_id_233.dfy

method {:testEntry} CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
  requires radius > 0.0 && height > 0.0
  ensures area == 2.0 * (radius * height) * 3.14
{
  area := (2.0 - radius * height) * 3.14;
}


method {:test} Test0() {
expect 1.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(1.0, 1.0);
expect r0 == 2.0 * (1.0 * 1.0) * 3.14;
}

// REPEAT 1 - TIME: 4.5979977 s

method {:test} Test1() {
expect 2.0 > 0.0 && 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(2.0, 2.0);
expect r0 == 2.0 * (2.0 * 2.0) * 3.14;
}

// REPEAT 2 - TIME: 6.1764101 s

method {:test} Test2() {
expect 3.0 > 0.0 && 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(3.0, 3.0);
expect r0 == 2.0 * (3.0 * 3.0) * 3.14;
}

// REPEAT 3 - TIME: 7.6748797 s

method {:test} Test3() {
expect 4.0 > 0.0 && 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(4.0, 4.0);
expect r0 == 2.0 * (4.0 * 4.0) * 3.14;
}

// REPEAT 4 - TIME: 9.0828098 s

method {:test} Test4() {
expect 5.0 > 0.0 && 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(5.0, 5.0);
expect r0 == 2.0 * (5.0 * 5.0) * 3.14;
}

// REPEAT 5 - TIME: 10.4527812 s

method {:test} Test5() {
expect 6.0 > 0.0 && 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(6.0, 6.0);
expect r0 == 2.0 * (6.0 * 6.0) * 3.14;
}

// REPEAT 6 - TIME: 11.4411876 s

method {:test} Test6() {
expect 7.0 > 0.0 && 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(7.0, 7.0);
expect r0 == 2.0 * (7.0 * 7.0) * 3.14;
}

// REPEAT 7 - TIME: 13.0037619 s

method {:test} Test7() {
expect 8.0 > 0.0 && 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(8.0, 8.0);
expect r0 == 2.0 * (8.0 * 8.0) * 3.14;
}

// REPEAT 8 - TIME: 14.0938281 s

method {:test} Test8() {
expect 9.0 > 0.0 && 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(9.0, 9.0);
expect r0 == 2.0 * (9.0 * 9.0) * 3.14;
}

// REPEAT 9 - TIME: 15.2989202 s

method {:test} Test9() {
expect 10.0 > 0.0 && 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(10.0, 10.0);
expect r0 == 2.0 * (10.0 * 10.0) * 3.14;
}

// REPEAT 10 - TIME: 16.5079089 s
