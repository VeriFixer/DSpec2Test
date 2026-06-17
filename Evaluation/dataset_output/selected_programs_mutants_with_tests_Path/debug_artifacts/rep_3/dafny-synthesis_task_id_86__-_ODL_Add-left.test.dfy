// dafny-synthesis_task_id_86.dfy

method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
  requires n >= 0
  ensures result == 3 * n * (n - 1) + 1
{
  result := 1;
}

method {:test} Test2() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(4);
expect r0 == 3 * 4 * (4 - 1) + 1;
}

// REPEAT 3 - TIME: 3.2032909 s
