method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}

method {:test} Test5() {
expect 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(44);
expect r0 == 5 * 44;
}

// REPEAT 6 - TIME: 9.0429089 s
