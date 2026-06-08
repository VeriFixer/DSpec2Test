method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    area := 6 * size * size;
}

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(4);
expect r0 == 6 * 4 * 4;
}

// REPEAT 4 - TIME: 6.3197421 s
