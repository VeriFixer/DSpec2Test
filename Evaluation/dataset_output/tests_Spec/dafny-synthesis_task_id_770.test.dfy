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

method {:test} Test0() {
expect 25 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(25);
expect r0 == 25 * (2 * 25 + 1) * (24 * 25 * 25 * 25 - 12 * 25 * 25 - 14 * 25 + 7) / 15;
}

// REPEAT 1 - TIME: 4.1815466 s

method {:test} Test1() {
expect 26 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(26);
expect r0 == 26 * (2 * 26 + 1) * (24 * 26 * 26 * 26 - 12 * 26 * 26 - 14 * 26 + 7) / 15;
}

// REPEAT 2 - TIME: 5.2420914 s

method {:test} Test2() {
expect 60 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(60);
expect r0 == 60 * (2 * 60 + 1) * (24 * 60 * 60 * 60 - 12 * 60 * 60 - 14 * 60 + 7) / 15;
}

// REPEAT 3 - TIME: 15.9720014 s

method {:test} Test3() {
expect 61 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(61);
expect r0 == 61 * (2 * 61 + 1) * (24 * 61 * 61 * 61 - 12 * 61 * 61 - 14 * 61 + 7) / 15;
}

// REPEAT 4 - TIME: 16.6440963 s

method {:test} Test4() {
expect 62 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(62);
expect r0 == 62 * (2 * 62 + 1) * (24 * 62 * 62 * 62 - 12 * 62 * 62 - 14 * 62 + 7) / 15;
}

// REPEAT 5 - TIME: 17.6046662 s

method {:test} Test5() {
expect 63 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(63);
expect r0 == 63 * (2 * 63 + 1) * (24 * 63 * 63 * 63 - 12 * 63 * 63 - 14 * 63 + 7) / 15;
}

// REPEAT 6 - TIME: 18.2200995 s

method {:test} Test6() {
expect 64 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(64);
expect r0 == 64 * (2 * 64 + 1) * (24 * 64 * 64 * 64 - 12 * 64 * 64 - 14 * 64 + 7) / 15;
}

// REPEAT 7 - TIME: 18.8402254 s
