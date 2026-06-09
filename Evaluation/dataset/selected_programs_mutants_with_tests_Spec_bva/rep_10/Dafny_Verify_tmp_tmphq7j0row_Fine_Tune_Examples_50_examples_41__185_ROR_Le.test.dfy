// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_41.dfy

method {:testEntry} main(n: int, k: int)
    returns (i: int, j: int)
  requires n >= 0
  requires k == 1 || k >= 0
  ensures k + i + j >= 2 * n
{
  i := 0;
  j := 0;
  while i <= n
    invariant 0 <= i <= n
    invariant j == i * (i + 1) / 2
  {
    i := i + 1;
    j := j + i;
  }
}

method {:test} Test32() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109 == 1 || 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7728, 109);
expect 109 + r0 + r1 >= 2 * 7728;
}

// REPEAT 10 - TIME: 17.7771569 s
