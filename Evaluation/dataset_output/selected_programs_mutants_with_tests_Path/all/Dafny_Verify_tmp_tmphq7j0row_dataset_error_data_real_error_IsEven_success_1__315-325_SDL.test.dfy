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
    r := !r;
  }
}


method {:test} Test0() {
expect 40 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(40);
expect r0 <==> even(40);
}

// REPEAT 1 - TIME: 8.3528374 s

method {:test} Test1() {
expect 41 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(41);
expect r0 <==> even(41);
}

// REPEAT 2 - TIME: 12.6848922 s

method {:test} Test2() {
expect 42 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(42);
expect r0 <==> even(42);
}

// REPEAT 3 - TIME: 16.9344459 s

method {:test} Test3() {
expect 43 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(43);
expect r0 <==> even(43);
}

// REPEAT 4 - TIME: 21.2166405 s

method {:test} Test4() {
expect 44 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(44);
expect r0 <==> even(44);
}

// REPEAT 5 - TIME: 25.3990902 s

method {:test} Test5() {
expect 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(45);
expect r0 <==> even(45);
}

// REPEAT 6 - TIME: 29.5727827 s

method {:test} Test6() {
expect 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(46);
expect r0 <==> even(46);
}

// REPEAT 7 - TIME: 33.727383 s

method {:test} Test7() {
expect 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(47);
expect r0 <==> even(47);
}

// REPEAT 8 - TIME: 38.6757822 s

method {:test} Test8() {
expect 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(48);
expect r0 <==> even(48);
}

// REPEAT 9 - TIME: 43.4311476 s

method {:test} Test9() {
expect 49 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(49);
expect r0 <==> even(49);
}

// REPEAT 10 - TIME: 48.7555699 s
