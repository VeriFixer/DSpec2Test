method {:testEntry} SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
    area := 4.0 * 3.14159265358979323846 * radius * radius;
}

method {:test} Test6() {
expect 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(101.0);
expect r0 == 4.0 * 3.14159265358979323846 * 101.0 * 101.0;
}

// REPEAT 2 - TIME: 5.6535752 s
