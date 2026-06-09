method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
{
    perimeter := 4 * side;
}

method {:test} Test5() {
expect 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(44);
expect r0 == 4 * 44;
}

// REPEAT 6 - TIME: 8.8516388 s
