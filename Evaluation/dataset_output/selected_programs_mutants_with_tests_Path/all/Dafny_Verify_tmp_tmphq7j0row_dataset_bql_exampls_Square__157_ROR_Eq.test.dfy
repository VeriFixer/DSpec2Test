// Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Square.dfy

method {:testEntry} square(n: int) returns (r: int)
  requires 0 <= n
  ensures r == n * n
{
  var x: int;
  var i: int;
  r := 0;
  i := 0;
  x := 1;
  while i == n
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

// REPEAT 1 - TIME: 6.4459935 s

method {:test} Test1() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 10.7709075 s

method {:test} Test2() {
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 13.9688648 s

method {:test} Test3() {
expect 0 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 16.8919115 s

method {:test} Test4() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 20.4892109 s

method {:test} Test5() {
expect 0 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 23.9900988 s

method {:test} Test6() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 27.4490239 s

method {:test} Test7() {
expect 0 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 32.050146 s

method {:test} Test8() {
expect 0 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 35.3880024 s

method {:test} Test9() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 39.1690351 s
