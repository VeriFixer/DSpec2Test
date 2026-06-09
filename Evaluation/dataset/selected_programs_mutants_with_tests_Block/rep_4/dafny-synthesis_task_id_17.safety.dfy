method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
{
    perimeter := 4 * side;
}

method {:test} Test3() {
expect 42 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(42);
expect r0 == 4 * 42;
}

// REPEAT 4 - TIME: 4.3210887 s
