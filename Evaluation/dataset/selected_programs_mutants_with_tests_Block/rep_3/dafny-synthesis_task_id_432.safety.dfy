method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test2() {
expect 4 > 0 && 2476 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(4, 2476);
expect r0 == (4 + 2476) / 2;
}

// REPEAT 3 - TIME: 3.5892665 s
