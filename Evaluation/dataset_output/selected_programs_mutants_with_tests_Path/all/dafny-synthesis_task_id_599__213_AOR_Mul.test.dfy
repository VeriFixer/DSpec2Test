// dafny-synthesis_task_id_599.dfy

method {:testEntry} SumAndAverage(n: int) returns (sum: int, average: real)
  requires n > 0
  ensures sum == n * (n + 1) / 2
  ensures average == sum as real / n as real
{
  sum := 0;
  for i := 1 to n * 1
    invariant 0 <= i <= n + 1
    invariant sum == (i - 1) * i / 2
  {
    sum := sum + i;
  }
  average := sum as real / n as real;
}


method {:test} Test0() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(4);
expect r0 == 4 * (4 + 1) / 2;
expect r1 == r0 as real / 4 as real;
}

// REPEAT 1 - TIME: 5.8428946 s

method {:test} Test1() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(8);
expect r0 == 8 * (8 + 1) / 2;
expect r1 == r0 as real / 8 as real;
}

// REPEAT 2 - TIME: 8.8896084 s

method {:test} Test2() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(9);
expect r0 == 9 * (9 + 1) / 2;
expect r1 == r0 as real / 9 as real;
}

// REPEAT 3 - TIME: 11.1542302 s

method {:test} Test3() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(10);
expect r0 == 10 * (10 + 1) / 2;
expect r1 == r0 as real / 10 as real;
}

// REPEAT 4 - TIME: 13.4805388 s

method {:test} Test4() {
expect 14 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(14);
expect r0 == 14 * (14 + 1) / 2;
expect r1 == r0 as real / 14 as real;
}

// REPEAT 5 - TIME: 16.4564505 s

method {:test} Test5() {
expect 17 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(17);
expect r0 == 17 * (17 + 1) / 2;
expect r1 == r0 as real / 17 as real;
}

// REPEAT 6 - TIME: 19.6900515 s

method {:test} Test6() {
expect 18 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(18);
expect r0 == 18 * (18 + 1) / 2;
expect r1 == r0 as real / 18 as real;
}

// REPEAT 7 - TIME: 22.6646557 s

method {:test} Test7() {
expect 19 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(19);
expect r0 == 19 * (19 + 1) / 2;
expect r1 == r0 as real / 19 as real;
}

// REPEAT 8 - TIME: 25.9176229 s

method {:test} Test8() {
expect 20 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(20);
expect r0 == 20 * (20 + 1) / 2;
expect r1 == r0 as real / 20 as real;
}

// REPEAT 9 - TIME: 29.5966059 s

method {:test} Test9() {
expect 21 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(21);
expect r0 == 21 * (21 + 1) / 2;
expect r1 == r0 as real / 21 as real;
}

// REPEAT 10 - TIME: 32.6300988 s
