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
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(0);
expect r0 == 0 * 0 * (0 + 1) * (0 + 1) / 4 - 0 * (0 + 1) / 2;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(100);
expect r0 == 100 * 100 * (100 + 1) * (100 + 1) / 4 - 100 * (100 + 1) / 2;
}

// REPEAT 1 - TIME: 9.0996962 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(101);
expect r0 == 101 * 101 * (101 + 1) * (101 + 1) / 4 - 101 * (101 + 1) / 2;
}

// REPEAT 2 - TIME: 10.2052655 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(102);
expect r0 == 102 * 102 * (102 + 1) * (102 + 1) / 4 - 102 * (102 + 1) / 2;
}

// REPEAT 3 - TIME: 11.1171413 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(103);
expect r0 == 103 * 103 * (103 + 1) * (103 + 1) / 4 - 103 * (103 + 1) / 2;
}

// REPEAT 4 - TIME: 12.1008392 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(104);
expect r0 == 104 * 104 * (104 + 1) * (104 + 1) / 4 - 104 * (104 + 1) / 2;
}

// REPEAT 5 - TIME: 13.0140616 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(105);
expect r0 == 105 * 105 * (105 + 1) * (105 + 1) / 4 - 105 * (105 + 1) / 2;
}

// REPEAT 6 - TIME: 13.9676403 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(106);
expect r0 == 106 * 106 * (106 + 1) * (106 + 1) / 4 - 106 * (106 + 1) / 2;
}

// REPEAT 7 - TIME: 14.8063089 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(107);
expect r0 == 107 * 107 * (107 + 1) * (107 + 1) / 4 - 107 * (107 + 1) / 2;
}

// REPEAT 8 - TIME: 15.6526706 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(108);
expect r0 == 108 * 108 * (108 + 1) * (108 + 1) / 4 - 108 * (108 + 1) / 2;
}

// REPEAT 9 - TIME: 16.5778095 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(109);
expect r0 == 109 * 109 * (109 + 1) * (109 + 1) / 4 - 109 * (109 + 1) / 2;
}

// REPEAT 10 - TIME: 17.4587291 s
