// dafny-synthesis_task_id_555.dfy

method {:testEntry} DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
  requires n >= 0
  ensures diff == n * n * (n + 1) * (n + 1) / 4 - n * (n + 1) / 2
{
  var sumCubes := 0;
  var sumNumbers := 0;
  for i := 1 to n + 1
    invariant 0 <= i <= n + 1
    invariant sumCubes == (i - 1) * (i - 1) * i * i / 4
    invariant sumNumbers == (i - 1) * i / 2
  {
    sumCubes := sumCubes + (i * i - i);
    sumNumbers := sumNumbers + i;
  }
  diff := sumCubes - sumNumbers;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(0);
expect r0 == 0 * 0 * (0 + 1) * (0 + 1) / 4 - 0 * (0 + 1) / 2;
}

// REPEAT 1 - TIME: 2.4783789 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(1);
expect r0 == 1 * 1 * (1 + 1) * (1 + 1) / 4 - 1 * (1 + 1) / 2;
}

// REPEAT 2 - TIME: 3.4971201 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(2);
expect r0 == 2 * 2 * (2 + 1) * (2 + 1) / 4 - 2 * (2 + 1) / 2;
}

// REPEAT 3 - TIME: 4.6737897 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(3);
expect r0 == 3 * 3 * (3 + 1) * (3 + 1) / 4 - 3 * (3 + 1) / 2;
}

// REPEAT 4 - TIME: 5.9284862 s

method {:test} Test4() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(6);
expect r0 == 6 * 6 * (6 + 1) * (6 + 1) / 4 - 6 * (6 + 1) / 2;
}

// REPEAT 5 - TIME: 7.1202586 s

method {:test} Test5() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(7);
expect r0 == 7 * 7 * (7 + 1) * (7 + 1) / 4 - 7 * (7 + 1) / 2;
}

// REPEAT 6 - TIME: 8.3085253 s

method {:test} Test6() {
expect 17 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(17);
expect r0 == 17 * 17 * (17 + 1) * (17 + 1) / 4 - 17 * (17 + 1) / 2;
}

// REPEAT 7 - TIME: 9.2146297 s

method {:test} Test7() {
expect 25 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(25);
expect r0 == 25 * 25 * (25 + 1) * (25 + 1) / 4 - 25 * (25 + 1) / 2;
}

// REPEAT 8 - TIME: 12.623766 s

method {:test} Test8() {
expect 26 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(26);
expect r0 == 26 * 26 * (26 + 1) * (26 + 1) / 4 - 26 * (26 + 1) / 2;
}

// REPEAT 9 - TIME: 13.4227631 s

method {:test} Test9() {
expect 32 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(32);
expect r0 == 32 * 32 * (32 + 1) * (32 + 1) / 4 - 32 * (32 + 1) / 2;
}

// REPEAT 10 - TIME: 17.01144 s
