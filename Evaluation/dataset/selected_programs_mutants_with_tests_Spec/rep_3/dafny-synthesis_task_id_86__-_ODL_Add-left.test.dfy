// dafny-synthesis_task_id_86.dfy

method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
  requires n >= 0
  ensures result == 3 * n * (n - 1) + 1
{
  result := 1;
}

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(2);
expect r0 == 3 * 2 * (2 - 1) + 1;
}

// REPEAT 3 - TIME: 3.7535748 s
