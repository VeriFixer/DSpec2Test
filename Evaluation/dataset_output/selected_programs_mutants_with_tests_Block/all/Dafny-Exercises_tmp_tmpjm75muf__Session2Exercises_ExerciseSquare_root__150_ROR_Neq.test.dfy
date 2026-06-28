// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy

method {:testEntry} mroot1(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) != n
    invariant r >= 0 && r * r <= n
    decreases n - r * r
  {
    r := r + 1;
  }
}

method {:testEntry} mroot2(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := n;
  while n < r * r
    invariant 0 <= r <= n && n < (r + 1) * (r + 1)
    invariant r * r <= n ==> n < (r + 1) * (r + 1)
    decreases r
  {
    r := r - 1;
  }
}

method {:testEntry} mroot3(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  var y: int;
  var h: int;
  r := 0;
  y := n + 1;
  while y != r + 1
    invariant r >= 0 && r * r <= n < y * y && y >= r + 1
    decreases y - r
  {
    h := (r + y) / 2;
    if h * h <= n {
      r := h;
    } else {
      y := h;
    }
  }
}


method {:test} Test0() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(1);
expect r0 >= 0 && r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}
method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(2);
expect r0 >= 0 && r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}
method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 1 - TIME: 3.4388157 s

method {:test} Test4() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(2);
expect r0 >= 0 && r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test6() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 5.434761 s

method {:test} Test8() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test10() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(24);
expect r0 >= 0 && r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}
method {:test} Test11() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 7.302506 s

method {:test} Test12() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test13() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test14() {
expect 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(48);
expect r0 >= 0 && r0 * r0 <= 48 < (r0 + 1) * (r0 + 1);
}
method {:test} Test15() {
expect 575 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(575);
expect r0 >= 0 && r0 * r0 <= 575 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 9.0011466 s

method {:test} Test16() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test17() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(6);
expect r0 >= 0 && r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}
method {:test} Test18() {
expect 624 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(624);
expect r0 >= 0 && r0 * r0 <= 624 < (r0 + 1) * (r0 + 1);
}
method {:test} Test19() {
expect 576 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(576);
expect r0 >= 0 && r0 * r0 <= 576 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 10.7327542 s

method {:test} Test20() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(6);
expect r0 >= 0 && r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}
method {:test} Test21() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(7);
expect r0 >= 0 && r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}
method {:test} Test22() {
expect 675 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(675);
expect r0 >= 0 && r0 * r0 <= 675 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 12.180222 s

method {:test} Test24() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(7);
expect r0 >= 0 && r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}
method {:test} Test25() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}
method {:test} Test26() {
expect 728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(728);
expect r0 >= 0 && r0 * r0 <= 728 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 13.5535455 s

method {:test} Test28() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}
method {:test} Test29() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}
method {:test} Test30() {
expect 783 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(783);
expect r0 >= 0 && r0 * r0 <= 783 < (r0 + 1) * (r0 + 1);
}
method {:test} Test31() {
expect 784 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(784);
expect r0 >= 0 && r0 * r0 <= 784 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 14.8819357 s

method {:test} Test32() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}
method {:test} Test33() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10);
expect r0 >= 0 && r0 * r0 <= 10 < (r0 + 1) * (r0 + 1);
}
method {:test} Test34() {
expect 840 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(840);
expect r0 >= 0 && r0 * r0 <= 840 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 16.2652987 s

method {:test} Test36() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10);
expect r0 >= 0 && r0 * r0 <= 10 < (r0 + 1) * (r0 + 1);
}
method {:test} Test37() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(11);
expect r0 >= 0 && r0 * r0 <= 11 < (r0 + 1) * (r0 + 1);
}
method {:test} Test38() {
expect 899 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(899);
expect r0 >= 0 && r0 * r0 <= 899 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 17.7170525 s
