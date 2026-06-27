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

// REPEAT 1 - TIME: 2.5047601 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(1);
expect r0 == 1 * 1 * (1 + 1) * (1 + 1) / 4 - 1 * (1 + 1) / 2;
}

// REPEAT 2 - TIME: 3.4528047 s

method {:test} Test2() {
expect 18 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(18);
expect r0 == 18 * 18 * (18 + 1) * (18 + 1) / 4 - 18 * (18 + 1) / 2;
}

// REPEAT 3 - TIME: 5.4778457 s

method {:test} Test3() {
expect 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(19);
expect r0 == 19 * 19 * (19 + 1) * (19 + 1) / 4 - 19 * (19 + 1) / 2;
}

// REPEAT 4 - TIME: 6.3955986 s

method {:test} Test4() {
expect 20 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(20);
expect r0 == 20 * 20 * (20 + 1) * (20 + 1) / 4 - 20 * (20 + 1) / 2;
}

// REPEAT 5 - TIME: 7.3587615 s

method {:test} Test5() {
expect 21 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(21);
expect r0 == 21 * 21 * (21 + 1) * (21 + 1) / 4 - 21 * (21 + 1) / 2;
}

// REPEAT 6 - TIME: 8.1781704 s

method {:test} Test6() {
expect 22 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(22);
expect r0 == 22 * 22 * (22 + 1) * (22 + 1) / 4 - 22 * (22 + 1) / 2;
}

// REPEAT 7 - TIME: 9.185678 s

method {:test} Test7() {
expect 23 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(23);
expect r0 == 23 * 23 * (23 + 1) * (23 + 1) / 4 - 23 * (23 + 1) / 2;
}

// REPEAT 8 - TIME: 9.9703058 s

method {:test} Test8() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(24);
expect r0 == 24 * 24 * (24 + 1) * (24 + 1) / 4 - 24 * (24 + 1) / 2;
}

// REPEAT 9 - TIME: 10.7358619 s

method {:test} Test9() {
expect 29 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(29);
expect r0 == 29 * 29 * (29 + 1) * (29 + 1) / 4 - 29 * (29 + 1) / 2;
}

// REPEAT 10 - TIME: 14.1108976 s
