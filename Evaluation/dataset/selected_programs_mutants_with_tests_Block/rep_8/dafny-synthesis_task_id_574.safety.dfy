method {:testEntry} CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
    area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
}

method {:test} Test7() {
expect 8.0 > 0.0 && 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(8.0, 8.0);
expect r0 == 2.0 * 3.14159265358979323846 * 8.0 * (8.0 + 8.0);
}

// REPEAT 8 - TIME: 6.6927565 s
