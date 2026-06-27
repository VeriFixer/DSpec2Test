// dafny-synthesis_task_id_599.dfy

method {:testEntry} SumAndAverage(n: int) returns (sum: int, average: real)
  requires n > 0
  ensures sum == n * (n + 1) / 2
  ensures average == sum as real / n as real
{
  for i := 1 to n + 1
    invariant 0 <= i <= n + 1
    invariant sum == (i - 1) * i / 2
  {
    sum := sum + i;
  }
  sum := 0;
  average := sum as real / n as real;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(1);
expect r0 == 1 * (1 + 1) / 2;
expect r1 == r0 as real / 1 as real;
}

// REPEAT 1 - TIME: 2.9415847 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(2);
expect r0 == 2 * (2 + 1) / 2;
expect r1 == r0 as real / 2 as real;
}

// REPEAT 2 - TIME: 4.0920171 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(3);
expect r0 == 3 * (3 + 1) / 2;
expect r1 == r0 as real / 3 as real;
}

// REPEAT 3 - TIME: 5.1598535 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(4);
expect r0 == 4 * (4 + 1) / 2;
expect r1 == r0 as real / 4 as real;
}

// REPEAT 4 - TIME: 6.1376769 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(5);
expect r0 == 5 * (5 + 1) / 2;
expect r1 == r0 as real / 5 as real;
}

// REPEAT 5 - TIME: 7.085797 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(6);
expect r0 == 6 * (6 + 1) / 2;
expect r1 == r0 as real / 6 as real;
}

// REPEAT 6 - TIME: 7.9943742 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(7);
expect r0 == 7 * (7 + 1) / 2;
expect r1 == r0 as real / 7 as real;
}

// REPEAT 7 - TIME: 8.77118 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(8);
expect r0 == 8 * (8 + 1) / 2;
expect r1 == r0 as real / 8 as real;
}

// REPEAT 8 - TIME: 9.4757005 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(9);
expect r0 == 9 * (9 + 1) / 2;
expect r1 == r0 as real / 9 as real;
}

// REPEAT 9 - TIME: 10.2380335 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(10);
expect r0 == 10 * (10 + 1) / 2;
expect r1 == r0 as real / 10 as real;
}

// REPEAT 10 - TIME: 11.0234414 s
