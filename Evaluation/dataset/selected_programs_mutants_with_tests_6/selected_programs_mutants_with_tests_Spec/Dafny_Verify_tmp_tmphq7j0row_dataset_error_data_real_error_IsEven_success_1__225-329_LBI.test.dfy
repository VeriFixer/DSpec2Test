// Dafny_Verify_tmp_tmphq7j0row_dataset_error_data_real_error_IsEven_success_1.dfy

function even(n: int): bool
  requires n >= 0
{
  if n == 0 then
    true
  else
    !even(n - 1)
}

method {:testEntry} is_even(n: int) returns (r: bool)
  requires n >= 0
  ensures r <==> even(n)
{
  var i: int := 0;
  r := true;
  while i < n
    invariant 0 <= i <= n
    invariant r <==> even(i)
  {
    break;
    r := !r;
    i := i + 1;
  }
}

method {:test} Test0() {
expect 7721 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7721);
expect r0 <==> even(7721);
}
method {:test} Test2() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7722);
expect r0 <==> even(7722);
}
method {:test} Test4() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7723);
expect r0 <==> even(7723);
}
method {:test} Test6() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7724);
expect r0 <==> even(7724);
}
method {:test} Test8() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7725);
expect r0 <==> even(7725);
}
method {:test} Test10() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7726);
expect r0 <==> even(7726);
}
