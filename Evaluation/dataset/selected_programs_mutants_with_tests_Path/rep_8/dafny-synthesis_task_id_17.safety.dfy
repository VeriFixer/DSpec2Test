method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
{
    perimeter := 4 * side;
}

method {:test} Test7() {
expect 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(46);
expect r0 == 4 * 46;
}

// REPEAT 8 - TIME: 11.6811344 s
