method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test4() {
expect 2482 > 0 && 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2482, 10);
expect r0 == (2482 + 10) / 2;
}

// REPEAT 5 - TIME: 6.9239676 s
