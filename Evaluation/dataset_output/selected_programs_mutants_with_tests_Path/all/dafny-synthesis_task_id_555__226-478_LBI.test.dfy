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
    break;
    sumCubes := sumCubes + i * i * i;
    sumNumbers := sumNumbers + i;
  }
  diff := sumCubes - sumNumbers;
}


method {:test} Test0() {
expect 63 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(63);
expect r0 == 63 * 63 * (63 + 1) * (63 + 1) / 4 - 63 * (63 + 1) / 2;
}

// REPEAT 1 - TIME: 7.2280387 s

method {:test} Test1() {
expect 64 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(64);
expect r0 == 64 * 64 * (64 + 1) * (64 + 1) / 4 - 64 * (64 + 1) / 2;
}

// REPEAT 2 - TIME: 10.4003365 s

method {:test} Test2() {
expect 65 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(65);
expect r0 == 65 * 65 * (65 + 1) * (65 + 1) / 4 - 65 * (65 + 1) / 2;
}

// REPEAT 3 - TIME: 13.3873599 s

method {:test} Test3() {
expect 66 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(66);
expect r0 == 66 * 66 * (66 + 1) * (66 + 1) / 4 - 66 * (66 + 1) / 2;
}

// REPEAT 4 - TIME: 16.6688584 s

method {:test} Test4() {
expect 67 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(67);
expect r0 == 67 * 67 * (67 + 1) * (67 + 1) / 4 - 67 * (67 + 1) / 2;
}

// REPEAT 5 - TIME: 19.8407524 s

method {:test} Test5() {
expect 68 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(68);
expect r0 == 68 * 68 * (68 + 1) * (68 + 1) / 4 - 68 * (68 + 1) / 2;
}

// REPEAT 6 - TIME: 22.8835005 s

method {:test} Test6() {
expect 73 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(73);
expect r0 == 73 * 73 * (73 + 1) * (73 + 1) / 4 - 73 * (73 + 1) / 2;
}

// REPEAT 7 - TIME: 28.0224045 s

method {:test} Test7() {
expect 74 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(74);
expect r0 == 74 * 74 * (74 + 1) * (74 + 1) / 4 - 74 * (74 + 1) / 2;
}

// REPEAT 8 - TIME: 31.0852761 s

method {:test} Test8() {
expect 75 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(75);
expect r0 == 75 * 75 * (75 + 1) * (75 + 1) / 4 - 75 * (75 + 1) / 2;
}

// REPEAT 9 - TIME: 34.7223834 s

method {:test} Test9() {
expect 76 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(76);
expect r0 == 76 * 76 * (76 + 1) * (76 + 1) / 4 - 76 * (76 + 1) / 2;
}

// REPEAT 10 - TIME: 37.8535152 s
