method {:testEntry} AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
{
    area := radius * radius;
}

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 4.2066946 s
