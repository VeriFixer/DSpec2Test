method {:testEntry} LateralSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 4 * size * size
{
    area := 4 * size * size;
}

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(2);
expect r0 == 4 * 2 * 2;
}

// REPEAT 2 - TIME: 3.4043614 s
