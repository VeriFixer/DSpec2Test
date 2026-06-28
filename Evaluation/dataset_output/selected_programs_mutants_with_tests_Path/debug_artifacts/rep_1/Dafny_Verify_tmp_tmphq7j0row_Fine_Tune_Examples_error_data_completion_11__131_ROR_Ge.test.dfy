// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_error_data_completion_11.dfy

method {:testEntry} main(x: int) returns (j: int, i: int)
  requires x > 0
  ensures j == 2 * x
{
  i := 0;
  j := 0;
  while i >= x
    invariant 0 <= i <= x
    invariant j == 2 * i
  {
    j := j + 2;
    i := i + 1;
  }
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(1);
expect r0 == 2 * 1;
}

// REPEAT 1 - TIME: 8.6529815 s
