method {:testEntry} CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
    area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
}

method {:test} Test1() {
expect 2.0 > 0.0 && 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(2.0, 2.0);
expect r0 == 2.0 * 3.14159265358979323846 * 2.0 * (2.0 + 2.0);
}

// REPEAT 2 - TIME: 3.8068664 s
