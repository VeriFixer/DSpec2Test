method {:testEntry} SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
    area := 4.0 * 3.14159265358979323846 * radius * radius;
}

method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(8.0);
expect r0 == 4.0 * 3.14159265358979323846 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 8.7229239 s
