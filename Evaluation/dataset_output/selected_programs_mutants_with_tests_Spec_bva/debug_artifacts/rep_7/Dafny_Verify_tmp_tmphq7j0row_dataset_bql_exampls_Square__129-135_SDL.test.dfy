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

method {:test} Test12() {
expect 0 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 15.0402415 s
