method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    area := 6 * size * size;
}

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(102);
expect r0 == 6 * 102 * 102;
}

// REPEAT 3 - TIME: 6.8777388 s
