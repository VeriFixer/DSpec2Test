// dafny-synthesis_task_id_135.dfy

method {:testEntry} NthHexagonalNumber(n: int) returns (hexNum: int)
  requires n >= 0
  ensures hexNum == n * (2 * n - 1)
{
  hexNum := n * 1;
}

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(2);
expect r0 == 2 * (2 * 2 - 1);
}

// REPEAT 3 - TIME: 3.2414529 s
