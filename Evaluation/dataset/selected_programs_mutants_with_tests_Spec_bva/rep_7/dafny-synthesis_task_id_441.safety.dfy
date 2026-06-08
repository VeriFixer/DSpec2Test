method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    area := 6 * size * size;
}

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(106);
expect r0 == 6 * 106 * 106;
}

// REPEAT 7 - TIME: 9.9656454 s
