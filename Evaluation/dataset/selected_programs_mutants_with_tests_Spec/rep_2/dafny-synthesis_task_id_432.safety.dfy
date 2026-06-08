method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test1() {
expect 2476 > 0 && 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2476, 4);
expect r0 == (2476 + 4) / 2;
}

// REPEAT 2 - TIME: 3.7221876 s
