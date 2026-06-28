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
    sum := i * i * i * i;
    i := 2;
  }
}


method {:test} Test0() {
expect 27 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(27);
expect r0 == 27 * (2 * 27 + 1) * (24 * 27 * 27 * 27 - 12 * 27 * 27 - 14 * 27 + 7) / 15;
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

// REPEAT 1 - TIME: 62.2871792 s

method {:test} Test5() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(101);
expect r0 == 101 * (2 * 101 + 1) * (24 * 101 * 101 * 101 - 12 * 101 * 101 - 14 * 101 + 7) / 15;
}

// REPEAT 2 - TIME: 63.3120902 s

method {:test} Test6() {
expect 623 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(623);
expect r0 == 623 * (2 * 623 + 1) * (24 * 623 * 623 * 623 - 12 * 623 * 623 - 14 * 623 + 7) / 15;
}

// REPEAT 3 - TIME: 93.2693625 s

method {:test} Test7() {
expect 624 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(624);
expect r0 == 624 * (2 * 624 + 1) * (24 * 624 * 624 * 624 - 12 * 624 * 624 - 14 * 624 + 7) / 15;
}

// REPEAT 4 - TIME: 94.0849324 s

method {:test} Test8() {
expect 625 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(625);
expect r0 == 625 * (2 * 625 + 1) * (24 * 625 * 625 * 625 - 12 * 625 * 625 - 14 * 625 + 7) / 15;
}

// REPEAT 5 - TIME: 94.9685288 s

method {:test} Test9() {
expect 626 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(626);
expect r0 == 626 * (2 * 626 + 1) * (24 * 626 * 626 * 626 - 12 * 626 * 626 - 14 * 626 + 7) / 15;
}

// REPEAT 6 - TIME: 95.6878939 s

method {:test} Test10() {
expect 627 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(627);
expect r0 == 627 * (2 * 627 + 1) * (24 * 627 * 627 * 627 - 12 * 627 * 627 - 14 * 627 + 7) / 15;
}

// REPEAT 7 - TIME: 96.4449249 s

method {:test} Test11() {
expect 628 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(628);
expect r0 == 628 * (2 * 628 + 1) * (24 * 628 * 628 * 628 - 12 * 628 * 628 - 14 * 628 + 7) / 15;
}

// REPEAT 8 - TIME: 97.1781102 s

method {:test} Test12() {
expect 629 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(629);
expect r0 == 629 * (2 * 629 + 1) * (24 * 629 * 629 * 629 - 12 * 629 * 629 - 14 * 629 + 7) / 15;
}

// REPEAT 9 - TIME: 97.8746592 s

method {:test} Test13() {
expect 630 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(630);
expect r0 == 630 * (2 * 630 + 1) * (24 * 630 * 630 * 630 - 12 * 630 * 630 - 14 * 630 + 7) / 15;
}

// REPEAT 10 - TIME: 98.9006558 s
