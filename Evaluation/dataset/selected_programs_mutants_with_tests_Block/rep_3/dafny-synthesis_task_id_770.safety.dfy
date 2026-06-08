method {:testEntry} SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
{
    sum := 0;
    var i := 1;
    for k := 0 to n
        invariant 0 <= k <= n
        invariant i == 2 * k + 1
        invariant sum == k * (2 * k + 1) * (24 * k * k * k - 12 * k * k  - 14 * k + 7) / 15
    {
        sum := sum + i * i * i * i;
        i := i + 2;
    }
}

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(3);
expect r0 == 3 * (2 * 3 + 1) * (24 * 3 * 3 * 3 - 12 * 3 * 3 - 14 * 3 + 7) / 15;
}

// REPEAT 3 - TIME: 4.0813715 s
