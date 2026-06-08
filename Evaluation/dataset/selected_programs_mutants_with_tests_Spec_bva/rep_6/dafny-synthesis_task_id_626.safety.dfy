method {:testEntry} AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
{
    area := radius * radius;
}

method {:test} Test11() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 10.0274552 s
