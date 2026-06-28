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
  while i > n
    invariant 0 <= i <= n
    invariant r <==> even(i)
  {
    r := !r;
    i := i + 1;
  }
}

method {:test} Test1() {
expect 41 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(41);
expect r0 <==> even(41);
}

// REPEAT 2 - TIME: 13.4029886 s
