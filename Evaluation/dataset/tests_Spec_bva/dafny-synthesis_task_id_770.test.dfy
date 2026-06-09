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
method {:test} Test1() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(1);
expect r0 == 1 * (2 * 1 + 1) * (24 * 1 * 1 * 1 - 12 * 1 * 1 - 14 * 1 + 7) / 15;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(100);
expect r0 == 100 * (2 * 100 + 1) * (24 * 100 * 100 * 100 - 12 * 100 * 100 - 14 * 100 + 7) / 15;
}
method {:test} Test3() {
expect 33 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(33);
expect r0 == 33 * (2 * 33 + 1) * (24 * 33 * 33 * 33 - 12 * 33 * 33 - 14 * 33 + 7) / 15;
}
method {:test} Test4() {
expect 27 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(27);
expect r0 == 27 * (2 * 27 + 1) * (24 * 27 * 27 * 27 - 12 * 27 * 27 - 14 * 27 + 7) / 15;
}

// REPEAT 1 - TIME: 51.7136629 s


// REPEAT 2 - TIME: 82.1572474 s

method {:test} Test5() {
expect 196 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(196);
expect r0 == 196 * (2 * 196 + 1) * (24 * 196 * 196 * 196 - 12 * 196 * 196 - 14 * 196 + 7) / 15;
}

// REPEAT 3 - TIME: 97.0449169 s

method {:test} Test6() {
expect 197 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(197);
expect r0 == 197 * (2 * 197 + 1) * (24 * 197 * 197 * 197 - 12 * 197 * 197 - 14 * 197 + 7) / 15;
}

// REPEAT 4 - TIME: 97.5927848 s

method {:test} Test7() {
expect 198 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(198);
expect r0 == 198 * (2 * 198 + 1) * (24 * 198 * 198 * 198 - 12 * 198 * 198 - 14 * 198 + 7) / 15;
}

// REPEAT 5 - TIME: 98.099081 s

method {:test} Test8() {
expect 199 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(199);
expect r0 == 199 * (2 * 199 + 1) * (24 * 199 * 199 * 199 - 12 * 199 * 199 - 14 * 199 + 7) / 15;
}

// REPEAT 6 - TIME: 98.580644 s

method {:test} Test9() {
expect 200 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(200);
expect r0 == 200 * (2 * 200 + 1) * (24 * 200 * 200 * 200 - 12 * 200 * 200 - 14 * 200 + 7) / 15;
}

// REPEAT 7 - TIME: 99.0637976 s

method {:test} Test10() {
expect 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(201);
expect r0 == 201 * (2 * 201 + 1) * (24 * 201 * 201 * 201 - 12 * 201 * 201 - 14 * 201 + 7) / 15;
}

// REPEAT 8 - TIME: 99.5699847 s

method {:test} Test11() {
expect 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(202);
expect r0 == 202 * (2 * 202 + 1) * (24 * 202 * 202 * 202 - 12 * 202 * 202 - 14 * 202 + 7) / 15;
}

// REPEAT 9 - TIME: 100.1766668 s

method {:test} Test12() {
expect 203 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(203);
expect r0 == 203 * (2 * 203 + 1) * (24 * 203 * 203 * 203 - 12 * 203 * 203 - 14 * 203 + 7) / 15;
}

// REPEAT 10 - TIME: 100.9883031 s
