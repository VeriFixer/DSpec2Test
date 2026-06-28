// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Mult.dfy

method {:testEntry} mult(a: int, b: int) returns (x: int)
  requires a >= 0 && b >= 0
  ensures x == a * b
{
  x := 0;
  var y := a;
  while y > 0
    invariant x == (a - y) * b
  {
    x := x * b;
    y := y - 1;
  }
}


method {:test} Test0() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(1, 0);
expect r0 == 1 * 0;
}

// REPEAT 1 - TIME: 1.8150788 s

method {:test} Test1() {
expect 2 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(2, 1);
expect r0 == 2 * 1;
}

// REPEAT 2 - TIME: 2.3876878 s

method {:test} Test2() {
expect 3 >= 0 && 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(3, 2);
expect r0 == 3 * 2;
}

// REPEAT 3 - TIME: 3.0927841 s

method {:test} Test3() {
expect 4 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(4, 3);
expect r0 == 4 * 3;
}

// REPEAT 4 - TIME: 3.7986361 s

method {:test} Test4() {
expect 5 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(5, 4);
expect r0 == 5 * 4;
}

// REPEAT 5 - TIME: 4.5945168 s

method {:test} Test5() {
expect 6 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(6, 5);
expect r0 == 6 * 5;
}

// REPEAT 6 - TIME: 5.3828804 s

method {:test} Test6() {
expect 7 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(7, 6);
expect r0 == 7 * 6;
}

// REPEAT 7 - TIME: 5.9935265 s

method {:test} Test7() {
expect 8 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(8, 7);
expect r0 == 8 * 7;
}

// REPEAT 8 - TIME: 6.6289408 s

method {:test} Test8() {
expect 9 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(9, 8);
expect r0 == 9 * 8;
}

// REPEAT 9 - TIME: 7.2155289 s

method {:test} Test9() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(10, 9);
expect r0 == 10 * 9;
}

// REPEAT 10 - TIME: 7.7077062 s
