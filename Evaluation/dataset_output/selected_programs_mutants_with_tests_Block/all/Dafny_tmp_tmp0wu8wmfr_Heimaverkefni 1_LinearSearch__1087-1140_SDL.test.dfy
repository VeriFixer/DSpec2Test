// Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 1_LinearSearch.dfy

method {:testEntry} SearchRecursive(a: seq<int>, i: int, j: int, x: int)
    returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
  decreases j - i
{
  if a[j - 1] == x {
    k := j - 1;
    return;
  } else {
    k := SearchRecursive(a, i, j - 1, x);
  }
}

method {:testEntry} SearchLoop(a: seq<int>, i: int, j: int, x: int)
    returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
  if i == j {
    return -1;
  }
  var t := j;
  while t > i
    invariant forall p | t <= p < j :: a[p] != x
    decreases t
  {
    if a[t - 1] == x {
      k := t - 1;
      return;
    } else {
      t := t - 1;
    }
  }
  k := -1;
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 28];
expect 0 <= 19 <= 21 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 19, 21, 26);
expect 19 <= r0 < 21 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 21 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 19 <= r < 21 :: seqint0[r] != 26;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 27];
expect 0 <= 8 <= 9 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 8, 9, 27);
expect 8 <= r0 < 9 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 9 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 8 <= r < 9 :: seqint0[r] != 27;
}
method {:test} Test2() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 1 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 1, 0);
expect 0 <= r0 < 1 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 1 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 1 :: seqint0[r] != 0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 25];
expect 0 <= 0 <= 9 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 9, 25);
expect 0 <= r0 < 9 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 25;
expect r0 != -1 ==> forall r | r0 < r < 9 :: seqint0[r] != 25;
expect r0 == -1 ==> forall r | 0 <= r < 9 :: seqint0[r] != 25;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}

// REPEAT 1 - TIME: 4.6965268 s

method {:test} Test6() {
var seqint0 : seq<int> := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 24];
expect 0 <= 20 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 20, 22, 25);
expect 20 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 25;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 25;
expect r0 == -1 ==> forall r | 20 <= r < 22 :: seqint0[r] != 25;
}
method {:test} Test7() {
var seqint0 : seq<int> := [4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30];
expect 0 <= 20 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 20, 22, 30);
expect 20 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 20 <= r < 22 :: seqint0[r] != 30;
}
method {:test} Test8() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 22 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 22, 22, 24);
expect 22 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 24;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 24;
expect r0 == -1 ==> forall r | 22 <= r < 22 :: seqint0[r] != 24;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 1 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 1, 10, 29);
expect 1 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 1 <= r < 10 :: seqint0[r] != 29;
}
method {:test} Test10() {
var seqint0 : seq<int> := [2, 29, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 1 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 1, 10, 29);
expect 1 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 1 <= r < 10 :: seqint0[r] != 29;
}
method {:test} Test11() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 10 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 10, 10, 26);
expect 10 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 10 <= r < 10 :: seqint0[r] != 26;
}

// REPEAT 2 - TIME: 7.592231 s

method {:test} Test12() {
var seqint0 : seq<int> := [117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34];
expect 0 <= 26 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 26, 27, 29);
expect 26 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 26 <= r < 27 :: seqint0[r] != 29;
}
method {:test} Test13() {
var seqint0 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 10, 0, 29];
expect 0 <= 23 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 24, 29);
expect 23 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 23 <= r < 24 :: seqint0[r] != 29;
}
method {:test} Test14() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0];
expect 0 <= 23 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 23, 33);
expect 23 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 23 <= r < 23 :: seqint0[r] != 33;
}
method {:test} Test15() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3];
expect 0 <= 11 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 12, 31);
expect 11 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 11 <= r < 12 :: seqint0[r] != 31;
}
method {:test} Test16() {
var seqint0 : seq<int> := [62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 5];
expect 0 <= 26 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 26, 27, 30);
expect 26 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 26 <= r < 27 :: seqint0[r] != 30;
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 3, 0, 0, 0, 0, 0, 0, 5, 0];
expect 0 <= 11 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 11, 27);
expect 11 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 11 <= r < 11 :: seqint0[r] != 27;
}

// REPEAT 3 - TIME: 10.2426443 s

method {:test} Test18() {
var seqint0 : seq<int> := [193, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 37];
expect 0 <= 28 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 28, 30, 31);
expect 28 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 28 <= r < 30 :: seqint0[r] != 31;
}
method {:test} Test19() {
var seqint0 : seq<int> := [22, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 16, 20, 0, 0, 18, 36];
expect 0 <= 27 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 27, 28, 36);
expect 27 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 27 <= r < 28 :: seqint0[r] != 36;
}
method {:test} Test20() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 13, 0, 0, 0, 0, 0, 0, 15, 0, 17, 0, 0, 19, 21];
expect 0 <= 28 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 28, 28, 31);
expect 28 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 28 <= r < 28 :: seqint0[r] != 31;
}
method {:test} Test21() {
var seqint0 : seq<int> := [117, 113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 108, 0, 0, 0, 111, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, 0, 0];
expect 0 <= 27 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 27, 28, 32);
expect 27 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 27 <= r < 28 :: seqint0[r] != 32;
}
method {:test} Test22() {
var seqint0 : seq<int> := [117, 0, 0, 109, 0, 0, 0, 0, 0, 110, 0, 10, 0, 0, 0, 111, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32];
expect 0 <= 27 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 27, 28, 32);
expect 27 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 27 <= r < 28 :: seqint0[r] != 32;
}
method {:test} Test23() {
var seqint0 : seq<int> := [13, 0, 0, 0, 0, 0, 0, 0, 0, 7, 9, 11, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 28 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 28, 28, 32);
expect 28 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 28 <= r < 28 :: seqint0[r] != 32;
}

// REPEAT 4 - TIME: 13.0988102 s

method {:test} Test24() {
var seqint0 : seq<int> := [276, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 270, 273];
expect 0 <= 24 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 29, 32);
expect 24 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 24 <= r < 29 :: seqint0[r] != 32;
}
method {:test} Test25() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 38, 42, 35];
expect 0 <= 24 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 29, 35);
expect 24 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 24 <= r < 29 :: seqint0[r] != 35;
}
method {:test} Test26() {
var seqint0 : seq<int> := [38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 33, 0];
expect 0 <= 29 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 29, 29, 35);
expect 29 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 29 <= r < 29 :: seqint0[r] != 35;
}
method {:test} Test27() {
var seqint0 : seq<int> := [205, 0, 0, 0, 0, 0, 0, 0, 0, 0, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 29 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 29, 30, 33);
expect 29 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 29 <= r < 30 :: seqint0[r] != 33;
}
method {:test} Test28() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 201, 0, 0, 0, 0, 0, 0, 0, 200, 0, 0, 0, 203, 34];
expect 0 <= 29 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 29, 30, 34);
expect 29 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 29 <= r < 30 :: seqint0[r] != 34;
}
method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 12, 0, 0, 0, 19, 0, 0, 0, 0, 0, 6, 17, 0, 21];
expect 0 <= 29 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 29, 29, 33);
expect 29 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 29 <= r < 29 :: seqint0[r] != 33;
}

// REPEAT 5 - TIME: 16.2245916 s

method {:test} Test30() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44];
expect 0 <= 25 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 26, 43);
expect 25 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 43;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 43;
expect r0 == -1 ==> forall r | 25 <= r < 26 :: seqint0[r] != 43;
}
method {:test} Test31() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 49, 41];
expect 0 <= 25 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 26, 41);
expect 25 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 41;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 41;
expect r0 == -1 ==> forall r | 25 <= r < 26 :: seqint0[r] != 41;
}
method {:test} Test32() {
var seqint0 : seq<int> := [43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39];
expect 0 <= 25 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 25, 44);
expect 25 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 44;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 44;
expect r0 == -1 ==> forall r | 25 <= r < 25 :: seqint0[r] != 44;
}
method {:test} Test33() {
var seqint0 : seq<int> := [285, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 283];
expect 0 <= 12 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 12, 13, 35);
expect 12 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 12 <= r < 13 :: seqint0[r] != 35;
}
method {:test} Test34() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 23, 0, 0, 0, 0, 282, 0, 20, 0, 16, 0, 0, 0, 0];
expect 0 <= 12 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 12, 13, 38);
expect 12 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 12 <= r < 13 :: seqint0[r] != 38;
}
method {:test} Test35() {
var seqint0 : seq<int> := [33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 23, 0, 28, 16, 8, 0, 26, 0, 0, 0, 0];
expect 0 <= 13 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 13, 13, 37);
expect 13 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 13 <= r < 13 :: seqint0[r] != 37;
}

// REPEAT 6 - TIME: 19.8210943 s

method {:test} Test36() {
var seqint0 : seq<int> := [412, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 17 <= 18 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 17, 18, 46);
expect 17 <= r0 < 18 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 18 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 17 <= r < 18 :: seqint0[r] != 46;
}
method {:test} Test37() {
var seqint0 : seq<int> := [50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 9 <= 18 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 9, 18, 46);
expect 9 <= r0 < 18 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 18 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 9 <= r < 18 :: seqint0[r] != 46;
}
method {:test} Test38() {
var seqint0 : seq<int> := [46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 10 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 10, 10, 48);
expect 10 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 48;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 48;
expect r0 == -1 ==> forall r | 10 <= r < 10 :: seqint0[r] != 48;
}
method {:test} Test39() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 14 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 15, 41);
expect 14 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 41;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 41;
expect r0 == -1 ==> forall r | 14 <= r < 15 :: seqint0[r] != 41;
}
method {:test} Test40() {
var seqint0 : seq<int> := [348, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 14 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 15, 41);
expect 14 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 41;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 41;
expect r0 == -1 ==> forall r | 14 <= r < 15 :: seqint0[r] != 41;
}
method {:test} Test41() {
var seqint0 : seq<int> := [27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 22];
expect 0 <= 14 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 14, 36);
expect 14 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 14 <= r < 14 :: seqint0[r] != 36;
}

// REPEAT 7 - TIME: 23.7711151 s

method {:test} Test42() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55];
expect 0 <= 18 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 18, 20, 54);
expect 18 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 54;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 54;
expect r0 == -1 ==> forall r | 18 <= r < 20 :: seqint0[r] != 54;
}
method {:test} Test43() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55];
expect 0 <= 18 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 18, 20, 55);
expect 18 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 55;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 55;
expect r0 == -1 ==> forall r | 18 <= r < 20 :: seqint0[r] != 55;
}
method {:test} Test44() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 16 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 16, 16, 51);
expect 16 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 51;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 51;
expect r0 == -1 ==> forall r | 16 <= r < 16 :: seqint0[r] != 51;
}
method {:test} Test45() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 15 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 15, 16, 43);
expect 15 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 43;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 43;
expect r0 == -1 ==> forall r | 15 <= r < 16 :: seqint0[r] != 43;
}
method {:test} Test46() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 15 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 15, 16, 43);
expect 15 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 43;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 43;
expect r0 == -1 ==> forall r | 15 <= r < 16 :: seqint0[r] != 43;
}
method {:test} Test47() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 16 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 16, 16, 42);
expect 16 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 42;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 42;
expect r0 == -1 ==> forall r | 16 <= r < 16 :: seqint0[r] != 42;
}

// REPEAT 8 - TIME: 27.5957704 s

method {:test} Test48() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 59];
expect 0 <= 15 <= 19 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 15, 19, 57);
expect 15 <= r0 < 19 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 57;
expect r0 != -1 ==> forall r | r0 < r < 19 :: seqint0[r] != 57;
expect r0 == -1 ==> forall r | 15 <= r < 19 :: seqint0[r] != 57;
}
method {:test} Test49() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58];
expect 0 <= 11 <= 19 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 11, 19, 58);
expect 11 <= r0 < 19 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 58;
expect r0 != -1 ==> forall r | r0 < r < 19 :: seqint0[r] != 58;
expect r0 == -1 ==> forall r | 11 <= r < 19 :: seqint0[r] != 58;
}
method {:test} Test50() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 11 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 11, 11, 53);
expect 11 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 53;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 53;
expect r0 == -1 ==> forall r | 11 <= r < 11 :: seqint0[r] != 53;
}
method {:test} Test51() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 17 <= 18 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 17, 18, 45);
expect 17 <= r0 < 18 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 45;
expect r0 != -1 ==> forall r | r0 < r < 18 :: seqint0[r] != 45;
expect r0 == -1 ==> forall r | 17 <= r < 18 :: seqint0[r] != 45;
}
method {:test} Test52() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 22, 23, 45);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 45;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 45;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 45;
}
method {:test} Test53() {
var seqint0 : seq<int> := [31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18];
expect 0 <= 17 <= 17 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 17, 17, 39);
expect 17 <= r0 < 17 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 17 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 17 <= r < 17 :: seqint0[r] != 39;
}

// REPEAT 9 - TIME: 31.8258119 s

method {:test} Test54() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 62, 0];
expect 0 <= 12 <= 17 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 12, 17, 61);
expect 12 <= r0 < 17 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 61;
expect r0 != -1 ==> forall r | r0 < r < 17 :: seqint0[r] != 61;
expect r0 == -1 ==> forall r | 12 <= r < 17 :: seqint0[r] != 61;
}
method {:test} Test55() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 0];
expect 0 <= 12 <= 17 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 12, 17, 56);
expect 12 <= r0 < 17 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 56;
expect r0 != -1 ==> forall r | r0 < r < 17 :: seqint0[r] != 56;
expect r0 == -1 ==> forall r | 12 <= r < 17 :: seqint0[r] != 56;
}
method {:test} Test56() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 12 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 12, 12, 56);
expect 12 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 56;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 56;
expect r0 == -1 ==> forall r | 12 <= r < 12 :: seqint0[r] != 56;
}
method {:test} Test57() {
var seqint0 : seq<int> := [473, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 23 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 23, 24, 40);
expect 23 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 23 <= r < 24 :: seqint0[r] != 40;
}
method {:test} Test58() {
var seqint0 : seq<int> := [475, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0];
expect 0 <= 23 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 23, 24, 48);
expect 23 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 48;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 48;
expect r0 == -1 ==> forall r | 23 <= r < 24 :: seqint0[r] != 48;
}
method {:test} Test59() {
var seqint0 : seq<int> := [24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 24 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 24, 24, 40);
expect 24 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 24 <= r < 24 :: seqint0[r] != 40;
}

// REPEAT 10 - TIME: 36.7387073 s
