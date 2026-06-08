method {:testEntry} CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * (radius * height) * 3.14
{
    area := 2.0 * (radius * height) * 3.14;
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

// REPEAT 1 - TIME: 6.3689115 s

method {:test} Test8() {
expect 101.0 > 0.0 && 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(101.0, 101.0);
expect r0 == 2.0 * (101.0 * 101.0) * 3.14;
}

// REPEAT 2 - TIME: 7.3324893 s

method {:test} Test9() {
expect 102.0 > 0.0 && 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(102.0, 102.0);
expect r0 == 2.0 * (102.0 * 102.0) * 3.14;
}

// REPEAT 3 - TIME: 8.2646175 s

method {:test} Test10() {
expect 103.0 > 0.0 && 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(103.0, 103.0);
expect r0 == 2.0 * (103.0 * 103.0) * 3.14;
}

// REPEAT 4 - TIME: 9.1756893 s

method {:test} Test11() {
expect 104.0 > 0.0 && 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(104.0, 104.0);
expect r0 == 2.0 * (104.0 * 104.0) * 3.14;
}

// REPEAT 5 - TIME: 10.1230549 s

method {:test} Test12() {
expect 105.0 > 0.0 && 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(105.0, 105.0);
expect r0 == 2.0 * (105.0 * 105.0) * 3.14;
}

// REPEAT 6 - TIME: 10.9484858 s

method {:test} Test13() {
expect 106.0 > 0.0 && 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(106.0, 106.0);
expect r0 == 2.0 * (106.0 * 106.0) * 3.14;
}

// REPEAT 7 - TIME: 11.9600614 s

method {:test} Test14() {
expect 107.0 > 0.0 && 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(107.0, 107.0);
expect r0 == 2.0 * (107.0 * 107.0) * 3.14;
}

// REPEAT 8 - TIME: 12.7694958 s

method {:test} Test15() {
expect 108.0 > 0.0 && 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(108.0, 108.0);
expect r0 == 2.0 * (108.0 * 108.0) * 3.14;
}

// REPEAT 9 - TIME: 13.4495128 s

method {:test} Test16() {
expect 109.0 > 0.0 && 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(109.0, 109.0);
expect r0 == 2.0 * (109.0 * 109.0) * 3.14;
}

// REPEAT 10 - TIME: 14.2777136 s
