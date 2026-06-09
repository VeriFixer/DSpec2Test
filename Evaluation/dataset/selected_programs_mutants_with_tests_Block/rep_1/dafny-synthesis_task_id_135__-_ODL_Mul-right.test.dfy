// dafny-synthesis_task_id_135.dfy

method {:testEntry} NthHexagonalNumber(n: int) returns (hexNum: int)
  requires n >= 0
  ensures hexNum == n * (2 * n - 1)
{
  hexNum := n;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(0);
expect r0 == 0 * (2 * 0 - 1);
}

// REPEAT 1 - TIME: 2.2229266 s
