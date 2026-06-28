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
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(0);
expect r0 == 0 * 0;
}
method {:test} Test2() {
expect 0 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(100);
expect r0 == 100 * 100;
}
method {:test} Test4() {
expect 0 <= 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 8.4920636 s
