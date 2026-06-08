method {:testEntry} SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
    area := 4.0 * 3.14159265358979323846 * radius * radius;
}

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(2.0);
expect r0 == 4.0 * 3.14159265358979323846 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 2.956935 s
