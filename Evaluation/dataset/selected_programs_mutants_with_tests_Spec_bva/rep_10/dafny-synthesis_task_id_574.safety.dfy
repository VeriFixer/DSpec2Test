method {:testEntry} CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
    area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
}

method {:test} Test16() {
expect 109.0 > 0.0 && 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(109.0, 109.0);
expect r0 == 2.0 * 3.14159265358979323846 * 109.0 * (109.0 + 109.0);
}

// REPEAT 10 - TIME: 12.3680567 s
