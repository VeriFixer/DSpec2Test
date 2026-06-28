// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Mult.dfy

method {:testEntry} mult(a: int, b: int) returns (x: int)
  requires a >= 0 && b >= 0
  ensures x == a * b
{
  x := 0;
  var y := a;
  while y == 0
    invariant x == (a - y) * b
  {
    x := x + b;
    y := y - 1;
  }
}


method {:test} Test0() {
expect 0 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(0, 0);
expect r0 == 0 * 0;
}

// REPEAT 1 - TIME: 7.7613247 s

method {:test} Test1() {
expect 1 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 12.3530288 s

method {:test} Test2() {
expect 2 >= 0 && 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(2, 2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 15.8319584 s

method {:test} Test3() {
expect 3 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 19.1521267 s

method {:test} Test4() {
expect 4 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(4, 4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 22.5594191 s

method {:test} Test5() {
expect 5 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(5, 5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 25.6517584 s

method {:test} Test6() {
expect 6 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(6, 6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 29.31109 s

method {:test} Test7() {
expect 7 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 32.4925785 s

method {:test} Test8() {
expect 8 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(8, 8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 36.3144442 s

method {:test} Test9() {
expect 9 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(9, 9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 39.8443842 s
