// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy

method {:testEntry} mroot1(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) > n
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
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test2() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test4() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test6() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test7() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test8() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test9() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test11() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test12() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test13() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test14() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test15() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(24);
expect r0 >= 0 && r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}
method {:test} Test16() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(24);
expect r0 >= 0 && r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}
method {:test} Test17() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(24);
expect r0 >= 0 && r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}
