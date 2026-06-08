method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test3() {
expect 5 > 0 && 2477 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(5, 2477);
expect r0 == (5 + 2477) / 2;
}

// REPEAT 4 - TIME: 4.5439584 s
