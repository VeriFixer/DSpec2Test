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

method {:test} Test1() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(4);
expect r0 == 4 * 4 * (4 + 1) * (4 + 1) / 4 - 4 * (4 + 1) / 2;
}

// REPEAT 2 - TIME: 3.9481059 s
