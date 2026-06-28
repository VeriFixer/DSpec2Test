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
  while false
    invariant 0 <= i <= n
    invariant r <==> even(i)
  {
    r := !r;
    i := i + 1;
  }
}


method {:test} Test0() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(1);
expect r0 <==> even(1);
}

// REPEAT 1 - TIME: 2.1888705 s

method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(2);
expect r0 <==> even(2);
}

// REPEAT 2 - TIME: 2.8396183 s

method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(3);
expect r0 <==> even(3);
}

// REPEAT 3 - TIME: 3.634493 s

method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(4);
expect r0 <==> even(4);
}

// REPEAT 4 - TIME: 4.4228957 s

method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(5);
expect r0 <==> even(5);
}

// REPEAT 5 - TIME: 5.0719288 s

method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(6);
expect r0 <==> even(6);
}

// REPEAT 6 - TIME: 5.7491784 s

method {:test} Test6() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7);
expect r0 <==> even(7);
}

// REPEAT 7 - TIME: 6.346368 s

method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(8);
expect r0 <==> even(8);
}

// REPEAT 8 - TIME: 7.0053177 s

method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(9);
expect r0 <==> even(9);
}

// REPEAT 9 - TIME: 7.608512 s

method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(10);
expect r0 <==> even(10);
}

// REPEAT 10 - TIME: 8.212585 s
