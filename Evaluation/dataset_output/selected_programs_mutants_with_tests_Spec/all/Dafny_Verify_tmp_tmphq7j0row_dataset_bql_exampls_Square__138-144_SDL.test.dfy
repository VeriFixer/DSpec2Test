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

// REPEAT 1 - TIME: 2.7546673 s

method {:test} Test1() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 3.7833297 s

method {:test} Test2() {
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 4.8084095 s

method {:test} Test3() {
expect 0 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 5.7156682 s

method {:test} Test4() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 6.6669766 s

method {:test} Test5() {
expect 0 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 7.5596465 s

method {:test} Test6() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 8.3637997 s

method {:test} Test7() {
expect 0 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 9.1619042 s

method {:test} Test8() {
expect 0 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 10.0415505 s

method {:test} Test9() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 10.8203412 s
