// dafny-synthesis_task_id_555.dfy

method {:testEntry} DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
  requires n >= 0
  ensures diff == n * n * (n + 1) * (n + 1) / 4 - n * (n + 1) / 2
{
  var sumCubes := 0;
  var sumNumbers := 0;
  for i := 1 to 1
    invariant 0 <= i <= n + 1
    invariant sumCubes == (i - 1) * (i - 1) * i * i / 4
    invariant sumNumbers == (i - 1) * i / 2
  {
    sumCubes := i * i * i;
    sumNumbers := i;
  }
  diff := sumCubes - sumNumbers;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(0);
expect r0 == 0 * 0 * (0 + 1) * (0 + 1) / 4 - 0 * (0 + 1) / 2;
}

// REPEAT 1 - TIME: 3.031176 s

method {:test} Test1() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(4);
expect r0 == 4 * 4 * (4 + 1) * (4 + 1) / 4 - 4 * (4 + 1) / 2;
}

// REPEAT 2 - TIME: 3.9481059 s

method {:test} Test2() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(5);
expect r0 == 5 * 5 * (5 + 1) * (5 + 1) / 4 - 5 * (5 + 1) / 2;
}

// REPEAT 3 - TIME: 4.8810536 s

method {:test} Test3() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(6);
expect r0 == 6 * 6 * (6 + 1) * (6 + 1) / 4 - 6 * (6 + 1) / 2;
}

// REPEAT 4 - TIME: 5.8156733 s

method {:test} Test4() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(7);
expect r0 == 7 * 7 * (7 + 1) * (7 + 1) / 4 - 7 * (7 + 1) / 2;
}

// REPEAT 5 - TIME: 6.7311745 s

method {:test} Test5() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(8);
expect r0 == 8 * 8 * (8 + 1) * (8 + 1) / 4 - 8 * (8 + 1) / 2;
}

// REPEAT 6 - TIME: 7.5973731 s

method {:test} Test6() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(9);
expect r0 == 9 * 9 * (9 + 1) * (9 + 1) / 4 - 9 * (9 + 1) / 2;
}

// REPEAT 7 - TIME: 8.4103325 s

method {:test} Test7() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(10);
expect r0 == 10 * 10 * (10 + 1) * (10 + 1) / 4 - 10 * (10 + 1) / 2;
}

// REPEAT 8 - TIME: 9.3080689 s

method {:test} Test8() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(11);
expect r0 == 11 * 11 * (11 + 1) * (11 + 1) / 4 - 11 * (11 + 1) / 2;
}

// REPEAT 9 - TIME: 10.1805167 s

method {:test} Test9() {
expect 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12);
expect r0 == 12 * 12 * (12 + 1) * (12 + 1) / 4 - 12 * (12 + 1) / 2;
}

// REPEAT 10 - TIME: 11.0243838 s
