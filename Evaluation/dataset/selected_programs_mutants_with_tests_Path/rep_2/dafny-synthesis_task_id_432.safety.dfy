method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test1() {
expect 3 > 0 && 2475 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(3, 2475);
expect r0 == (3 + 2475) / 2;
}

// REPEAT 2 - TIME: 1.5570182 s
