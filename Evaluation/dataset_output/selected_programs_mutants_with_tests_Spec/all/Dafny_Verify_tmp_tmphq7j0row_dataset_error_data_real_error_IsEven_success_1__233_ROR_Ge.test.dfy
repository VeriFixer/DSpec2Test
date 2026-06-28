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
  while i >= n
    invariant 0 <= i <= n
    invariant r <==> even(i)
  {
    r := !r;
    i := i + 1;
  }
}


method {:test} Test0() {
expect 7721 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7721);
expect r0 <==> even(7721);
}

// REPEAT 1 - TIME: 3.803145 s

method {:test} Test2() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7722);
expect r0 <==> even(7722);
}

// REPEAT 2 - TIME: 5.3387118 s

method {:test} Test4() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7723);
expect r0 <==> even(7723);
}

// REPEAT 3 - TIME: 6.7237063 s

method {:test} Test6() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7724);
expect r0 <==> even(7724);
}

// REPEAT 4 - TIME: 8.1909762 s

method {:test} Test8() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7725);
expect r0 <==> even(7725);
}

// REPEAT 5 - TIME: 9.5471131 s

method {:test} Test10() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7726);
expect r0 <==> even(7726);
}

// REPEAT 6 - TIME: 10.6059237 s

method {:test} Test12() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7727);
expect r0 <==> even(7727);
}

// REPEAT 7 - TIME: 11.4988577 s

method {:test} Test14() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7728);
expect r0 <==> even(7728);
}

// REPEAT 8 - TIME: 12.334631 s

method {:test} Test16() {
expect 7729 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7729);
expect r0 <==> even(7729);
}

// REPEAT 9 - TIME: 13.1441452 s

method {:test} Test18() {
expect 7730 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7730);
expect r0 <==> even(7730);
}

// REPEAT 10 - TIME: 13.9919514 s
