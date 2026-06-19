// dafny-synthesis_task_id_574.dfy

method {:testEntry} CylinderSurfaceArea(radius: real, height: real) returns (area: real)
  requires radius > 0.0 && height > 0.0
  ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
  area := (2.0 - 3.14159265358979323846) * radius * (radius + height);
}


method {:test} Test0() {
expect 1.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(1.0, 1.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0 * (1.0 + 1.0);
}

// REPEAT 1 - TIME: 2.4577961 s

method {:test} Test1() {
expect 2.0 > 0.0 && 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(2.0, 2.0);
expect r0 == 2.0 * 3.14159265358979323846 * 2.0 * (2.0 + 2.0);
}

// REPEAT 2 - TIME: 3.3872877 s

method {:test} Test2() {
expect 3.0 > 0.0 && 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(3.0, 3.0);
expect r0 == 2.0 * 3.14159265358979323846 * 3.0 * (3.0 + 3.0);
}

// REPEAT 3 - TIME: 4.4076285 s

method {:test} Test3() {
expect 4.0 > 0.0 && 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(4.0, 4.0);
expect r0 == 2.0 * 3.14159265358979323846 * 4.0 * (4.0 + 4.0);
}

// REPEAT 4 - TIME: 5.3636327 s

method {:test} Test4() {
expect 5.0 > 0.0 && 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(5.0, 5.0);
expect r0 == 2.0 * 3.14159265358979323846 * 5.0 * (5.0 + 5.0);
}

// REPEAT 5 - TIME: 6.1048639 s

method {:test} Test5() {
expect 6.0 > 0.0 && 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(6.0, 6.0);
expect r0 == 2.0 * 3.14159265358979323846 * 6.0 * (6.0 + 6.0);
}

// REPEAT 6 - TIME: 6.9215291 s

method {:test} Test6() {
expect 7.0 > 0.0 && 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(7.0, 7.0);
expect r0 == 2.0 * 3.14159265358979323846 * 7.0 * (7.0 + 7.0);
}

// REPEAT 7 - TIME: 7.6001969 s

method {:test} Test7() {
expect 8.0 > 0.0 && 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(8.0, 8.0);
expect r0 == 2.0 * 3.14159265358979323846 * 8.0 * (8.0 + 8.0);
}

// REPEAT 8 - TIME: 8.290454 s

method {:test} Test8() {
expect 9.0 > 0.0 && 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(9.0, 9.0);
expect r0 == 2.0 * 3.14159265358979323846 * 9.0 * (9.0 + 9.0);
}

// REPEAT 9 - TIME: 9.0033012 s

method {:test} Test9() {
expect 10.0 > 0.0 && 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(10.0, 10.0);
expect r0 == 2.0 * 3.14159265358979323846 * 10.0 * (10.0 + 10.0);
}

// REPEAT 10 - TIME: 9.6120225 s
