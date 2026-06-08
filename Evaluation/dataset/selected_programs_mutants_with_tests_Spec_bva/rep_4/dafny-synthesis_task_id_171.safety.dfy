method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(103);
expect r0 == 5 * 103;
}

// REPEAT 4 - TIME: 7.8254936 s
