// dafny-synthesis_task_id_770.dfy

method {:testEntry} SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
  requires n > 0
  ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
  sum := 0;
  var i := 1;
  for k := 0 to n
    invariant 0 <= k <= n
    invariant i == 2 * k + 1
    invariant sum == k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15
  {
    sum := sum + (i * i * i - i);
    i := i + 2;
  }
}


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
expect 27 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(27);
expect r0 == 27 * (2 * 27 + 1) * (24 * 27 * 27 * 27 - 12 * 27 * 27 - 14 * 27 + 7) / 15;
}

// REPEAT 1 - TIME: 5.2053585 s

method {:test} Test1() {
expect 28 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(28);
expect r0 == 28 * (2 * 28 + 1) * (24 * 28 * 28 * 28 - 12 * 28 * 28 - 14 * 28 + 7) / 15;
}

// REPEAT 2 - TIME: 6.1104237 s

method {:test} Test2() {
expect 48 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(48);
expect r0 == 48 * (2 * 48 + 1) * (24 * 48 * 48 * 48 - 12 * 48 * 48 - 14 * 48 + 7) / 15;
}

// REPEAT 3 - TIME: 7.249168 s

method {:test} Test3() {
expect 49 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(49);
expect r0 == 49 * (2 * 49 + 1) * (24 * 49 * 49 * 49 - 12 * 49 * 49 - 14 * 49 + 7) / 15;
}

// REPEAT 4 - TIME: 8.3165708 s

method {:test} Test4() {
expect 50 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(50);
expect r0 == 50 * (2 * 50 + 1) * (24 * 50 * 50 * 50 - 12 * 50 * 50 - 14 * 50 + 7) / 15;
}

// REPEAT 5 - TIME: 9.5499166 s

method {:test} Test5() {
expect 51 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(51);
expect r0 == 51 * (2 * 51 + 1) * (24 * 51 * 51 * 51 - 12 * 51 * 51 - 14 * 51 + 7) / 15;
}

// REPEAT 6 - TIME: 10.2957636 s

method {:test} Test6() {
expect 52 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(52);
expect r0 == 52 * (2 * 52 + 1) * (24 * 52 * 52 * 52 - 12 * 52 * 52 - 14 * 52 + 7) / 15;
}

// REPEAT 7 - TIME: 11.2099173 s
