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
expect 60 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(60);
expect r0 == 60 * (2 * 60 + 1) * (24 * 60 * 60 * 60 - 12 * 60 * 60 - 14 * 60 + 7) / 15;
}

// REPEAT 3 - TIME: 17.3001189 s
