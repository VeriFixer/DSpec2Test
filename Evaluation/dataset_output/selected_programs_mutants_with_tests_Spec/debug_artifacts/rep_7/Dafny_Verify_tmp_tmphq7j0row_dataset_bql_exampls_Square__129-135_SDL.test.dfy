// Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Square.dfy

method {:testEntry} square(n: int) returns (r: int)
  requires 0 <= n
  ensures r == n * n
{
  var x: int;
  var i: int;
  r := 0;
  x := 1;
  while i < n
    invariant i <= n
    invariant r == i * i
    invariant x == 2 * i + 1
  {
    r := r + x;
    x := x + 2;
    i := i + 1;
  }
}

method {:test} Test6() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 8.3637997 s
