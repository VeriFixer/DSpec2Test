method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(1);
expect r0 == 5 * 1;
}

// REPEAT 1 - TIME: 2.7156382 s
