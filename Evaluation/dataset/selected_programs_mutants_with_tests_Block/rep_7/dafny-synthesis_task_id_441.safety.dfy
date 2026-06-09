method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    area := 6 * size * size;
}

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(7);
expect r0 == 6 * 7 * 7;
}

// REPEAT 7 - TIME: 6.2796553 s
