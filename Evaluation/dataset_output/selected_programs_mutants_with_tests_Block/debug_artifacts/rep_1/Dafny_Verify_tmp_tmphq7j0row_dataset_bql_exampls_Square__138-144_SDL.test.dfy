// Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Square.dfy

method {:testEntry} square(n: int) returns (r: int)
  requires 0 <= n
  ensures r == n * n
{
  var x: int;
  var i: int;
  r := 0;
  i := 0;
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

method {:test} Test0() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(1);
expect r0 == 1 * 1;
}

// REPEAT 1 - TIME: 2.017623 s
