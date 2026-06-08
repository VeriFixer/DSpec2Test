method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(108);
expect r0 == 5 * 108;
}

// REPEAT 9 - TIME: 11.1289183 s
