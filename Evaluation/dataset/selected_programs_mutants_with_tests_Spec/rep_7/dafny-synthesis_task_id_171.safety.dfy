method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}

method {:test} Test6() {
expect 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(45);
expect r0 == 5 * 45;
}

// REPEAT 7 - TIME: 7.0620465 s
