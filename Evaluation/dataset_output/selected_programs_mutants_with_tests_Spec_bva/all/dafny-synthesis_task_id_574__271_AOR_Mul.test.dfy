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

// REPEAT 1 - TIME: 7.8362571 s

method {:test} Test8() {
expect 101.0 > 0.0 && 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(101.0, 101.0);
expect r0 == 2.0 * 3.14159265358979323846 * 101.0 * (101.0 + 101.0);
}

// REPEAT 2 - TIME: 9.4440764 s

method {:test} Test9() {
expect 102.0 > 0.0 && 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(102.0, 102.0);
expect r0 == 2.0 * 3.14159265358979323846 * 102.0 * (102.0 + 102.0);
}

// REPEAT 3 - TIME: 10.7301722 s

method {:test} Test10() {
expect 103.0 > 0.0 && 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(103.0, 103.0);
expect r0 == 2.0 * 3.14159265358979323846 * 103.0 * (103.0 + 103.0);
}

// REPEAT 4 - TIME: 11.7787118 s

method {:test} Test11() {
expect 104.0 > 0.0 && 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(104.0, 104.0);
expect r0 == 2.0 * 3.14159265358979323846 * 104.0 * (104.0 + 104.0);
}

// REPEAT 5 - TIME: 12.7385594 s

method {:test} Test12() {
expect 105.0 > 0.0 && 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(105.0, 105.0);
expect r0 == 2.0 * 3.14159265358979323846 * 105.0 * (105.0 + 105.0);
}

// REPEAT 6 - TIME: 13.5125058 s

method {:test} Test13() {
expect 106.0 > 0.0 && 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(106.0, 106.0);
expect r0 == 2.0 * 3.14159265358979323846 * 106.0 * (106.0 + 106.0);
}

// REPEAT 7 - TIME: 14.3264395 s

method {:test} Test14() {
expect 107.0 > 0.0 && 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(107.0, 107.0);
expect r0 == 2.0 * 3.14159265358979323846 * 107.0 * (107.0 + 107.0);
}

// REPEAT 8 - TIME: 15.1884359 s

method {:test} Test15() {
expect 108.0 > 0.0 && 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(108.0, 108.0);
expect r0 == 2.0 * 3.14159265358979323846 * 108.0 * (108.0 + 108.0);
}

// REPEAT 9 - TIME: 15.8818172 s

method {:test} Test16() {
expect 109.0 > 0.0 && 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(109.0, 109.0);
expect r0 == 2.0 * 3.14159265358979323846 * 109.0 * (109.0 + 109.0);
}

// REPEAT 10 - TIME: 16.6869788 s
