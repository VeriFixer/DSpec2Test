method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test10() {
expect 2478 > 0 && 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2478, 202);
expect r0 == (2478 + 202) / 2;
}

// REPEAT 3 - TIME: 7.7577759 s
