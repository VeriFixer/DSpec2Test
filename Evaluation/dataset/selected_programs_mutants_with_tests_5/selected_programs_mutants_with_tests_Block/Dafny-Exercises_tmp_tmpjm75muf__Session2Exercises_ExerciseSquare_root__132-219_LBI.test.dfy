// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy

method {:testEntry} mroot1(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) <= n
    invariant r >= 0 && r * r <= n
    decreases n - r * r
  {
    break;
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
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test11() {
expect 143 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(143);
expect r0 >= 0 && r0 * r0 <= 143 < (r0 + 1) * (r0 + 1);
}
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
expect 144 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(144);
expect r0 >= 0 && r0 * r0 <= 144 < (r0 + 1) * (r0 + 1);
}
method {:test} Test15() {
expect 576 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(576);
expect r0 >= 0 && r0 * r0 <= 576 < (r0 + 1) * (r0 + 1);
}
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
