method {:testEntry} CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
    area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
}

method {:test} Test6() {
expect 7.0 > 0.0 && 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(7.0, 7.0);
expect r0 == 2.0 * 3.14159265358979323846 * 7.0 * (7.0 + 7.0);
}

// REPEAT 7 - TIME: 6.0808829 s
