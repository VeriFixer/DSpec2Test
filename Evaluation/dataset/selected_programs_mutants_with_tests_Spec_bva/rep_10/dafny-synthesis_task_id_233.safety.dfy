method {:testEntry} CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * (radius * height) * 3.14
{
    area := 2.0 * (radius * height) * 3.14;
}

method {:test} Test16() {
expect 109.0 > 0.0 && 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(109.0, 109.0);
expect r0 == 2.0 * (109.0 * 109.0) * 3.14;
}

// REPEAT 10 - TIME: 14.2777136 s
