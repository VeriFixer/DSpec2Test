method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
{
    perimeter := 4 * side;
}

method {:test} Test4() {
expect 43 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(43);
expect r0 == 4 * 43;
}

// REPEAT 5 - TIME: 9.1714885 s
