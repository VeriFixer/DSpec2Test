method {:testEntry} CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * (radius * height) * 3.14
{
    area := 2.0 * (radius * height) * 3.14;
}

method {:test} Test8() {
expect 9.0 > 0.0 && 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(9.0, 9.0);
expect r0 == 2.0 * (9.0 * 9.0) * 3.14;
}

// REPEAT 9 - TIME: 8.7216266 s
