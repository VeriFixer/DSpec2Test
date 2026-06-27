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

method {:test} Test14() {
expect 0 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 12.2761492 s
