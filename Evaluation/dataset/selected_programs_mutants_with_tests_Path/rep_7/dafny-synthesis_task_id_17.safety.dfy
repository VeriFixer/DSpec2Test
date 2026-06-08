method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
{
    perimeter := 4 * side;
}

method {:test} Test6() {
expect 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(45);
expect r0 == 4 * 45;
}

// REPEAT 7 - TIME: 10.9049329 s
