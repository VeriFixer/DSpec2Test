method {:testEntry} SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
    area := 4.0 * 3.14159265358979323846 * radius * radius;
}

method {:test} Test8() {
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(103.0);
expect r0 == 4.0 * 3.14159265358979323846 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 7.7154291 s
