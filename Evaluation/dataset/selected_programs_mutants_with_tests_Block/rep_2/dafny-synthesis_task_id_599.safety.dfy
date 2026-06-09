method {:testEntry} SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
{
    sum := 0;
    for i := 1 to n + 1
    invariant 0 <= i <= n + 1
    invariant sum == (i - 1) * i / 2
    {
        sum := sum + i;
    }
    average := sum as real / n as real;
}

method {:test} Test1() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(8);
expect r0 == 8 * (8 + 1) / 2;
expect r1 == r0 as real / 8 as real;
}

// REPEAT 2 - TIME: 3.3796915 s
