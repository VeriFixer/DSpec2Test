method {:testEntry} AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
{
    area := radius * radius;
}

method {:test} Test9() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 8.6195242 s
