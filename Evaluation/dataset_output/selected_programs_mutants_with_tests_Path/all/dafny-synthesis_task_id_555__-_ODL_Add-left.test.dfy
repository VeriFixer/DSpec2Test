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
expect 63 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(63);
expect r0 == 63 * 63 * (63 + 1) * (63 + 1) / 4 - 63 * (63 + 1) / 2;
}

// REPEAT 1 - TIME: 5.9122467 s

method {:test} Test1() {
expect 12665432492634448545274086 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274086);
expect r0 == 12665432492634448545274086 * 12665432492634448545274086 * (12665432492634448545274086 + 1) * (12665432492634448545274086 + 1) / 4 - 12665432492634448545274086 * (12665432492634448545274086 + 1) / 2;
}

// REPEAT 2 - TIME: 11.5598187 s

method {:test} Test2() {
expect 12665432492634448545274087 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274087);
expect r0 == 12665432492634448545274087 * 12665432492634448545274087 * (12665432492634448545274087 + 1) * (12665432492634448545274087 + 1) / 4 - 12665432492634448545274087 * (12665432492634448545274087 + 1) / 2;
}

// REPEAT 3 - TIME: 13.9434217 s

method {:test} Test3() {
expect 12665432492634448545274088 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274088);
expect r0 == 12665432492634448545274088 * 12665432492634448545274088 * (12665432492634448545274088 + 1) * (12665432492634448545274088 + 1) / 4 - 12665432492634448545274088 * (12665432492634448545274088 + 1) / 2;
}

// REPEAT 4 - TIME: 16.3981789 s

method {:test} Test4() {
expect 12665432492634448545274097 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274097);
expect r0 == 12665432492634448545274097 * 12665432492634448545274097 * (12665432492634448545274097 + 1) * (12665432492634448545274097 + 1) / 4 - 12665432492634448545274097 * (12665432492634448545274097 + 1) / 2;
}

// REPEAT 5 - TIME: 21.1108028 s

method {:test} Test5() {
expect 12665432492634448545274098 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274098);
expect r0 == 12665432492634448545274098 * 12665432492634448545274098 * (12665432492634448545274098 + 1) * (12665432492634448545274098 + 1) / 4 - 12665432492634448545274098 * (12665432492634448545274098 + 1) / 2;
}

// REPEAT 6 - TIME: 24.1778563 s

method {:test} Test6() {
expect 12665432492634448545274101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274101);
expect r0 == 12665432492634448545274101 * 12665432492634448545274101 * (12665432492634448545274101 + 1) * (12665432492634448545274101 + 1) / 4 - 12665432492634448545274101 * (12665432492634448545274101 + 1) / 2;
}

// REPEAT 7 - TIME: 30.5384116 s

method {:test} Test7() {
expect 12665432492634448545274103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274103);
expect r0 == 12665432492634448545274103 * 12665432492634448545274103 * (12665432492634448545274103 + 1) * (12665432492634448545274103 + 1) / 4 - 12665432492634448545274103 * (12665432492634448545274103 + 1) / 2;
}

// REPEAT 8 - TIME: 33.6596228 s

method {:test} Test8() {
expect 12665432492634448545274104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274104);
expect r0 == 12665432492634448545274104 * 12665432492634448545274104 * (12665432492634448545274104 + 1) * (12665432492634448545274104 + 1) / 4 - 12665432492634448545274104 * (12665432492634448545274104 + 1) / 2;
}

// REPEAT 9 - TIME: 39.3753537 s

method {:test} Test9() {
expect 12665432492634448545274105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274105);
expect r0 == 12665432492634448545274105 * 12665432492634448545274105 * (12665432492634448545274105 + 1) * (12665432492634448545274105 + 1) / 4 - 12665432492634448545274105 * (12665432492634448545274105 + 1) / 2;
}

// REPEAT 10 - TIME: 42.048394 s
