method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}

method {:test} Test7() {
expect 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(46);
expect r0 == 5 * 46;
}

// REPEAT 8 - TIME: 10.8779019 s
