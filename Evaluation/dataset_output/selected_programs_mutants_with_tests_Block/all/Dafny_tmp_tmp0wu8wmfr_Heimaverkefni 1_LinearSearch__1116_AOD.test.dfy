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
  if j == i {
    k := 1;
    return;
  }
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

// REPEAT 1 - TIME: 4.5118789 s

method {:test} Test6() {
var seqint0 : seq<int> := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30];
expect 0 <= 20 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 20, 22, 29);
expect 20 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 20 <= r < 22 :: seqint0[r] != 29;
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
var seqint0 : seq<int> := [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 22 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 22, 22, 30);
expect 22 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 22 <= r < 22 :: seqint0[r] != 30;
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
var seqint0 : seq<int> := [0, 29, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 1 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 1, 10, 29);
expect 1 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 1 <= r < 10 :: seqint0[r] != 29;
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 10 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 10, 10, 26);
expect 10 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 10 <= r < 10 :: seqint0[r] != 26;
}

// REPEAT 2 - TIME: 7.4041492 s

method {:test} Test12() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 35];
expect 0 <= 28 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 28, 30, 33);
expect 28 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 28 <= r < 30 :: seqint0[r] != 33;
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 10, 31];
expect 0 <= 23 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 24, 31);
expect 23 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 23 <= r < 24 :: seqint0[r] != 31;
}
method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 9, 0];
expect 0 <= 23 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 23, 24);
expect 23 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 24;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 24;
expect r0 == -1 ==> forall r | 23 <= r < 23 :: seqint0[r] != 24;
}
method {:test} Test15() {
var seqint0 : seq<int> := [51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
expect 0 <= 11 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 12, 28);
expect 11 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 28;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 28;
expect r0 == -1 ==> forall r | 11 <= r < 12 :: seqint0[r] != 28;
}
method {:test} Test16() {
var seqint0 : seq<int> := [48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 5, 0, 0, 0, 0, 0, 0, 3];
expect 0 <= 13 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 13, 14, 27);
expect 13 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 13 <= r < 14 :: seqint0[r] != 27;
}
method {:test} Test17() {
var seqint0 : seq<int> := [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 11 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 11, 27);
expect 11 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 11 <= r < 11 :: seqint0[r] != 27;
}

// REPEAT 3 - TIME: 9.8784578 s

method {:test} Test18() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 171, 0, 0, 34, 14];
expect 0 <= 24 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 29, 32);
expect 24 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 24 <= r < 29 :: seqint0[r] != 32;
}
method {:test} Test19() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 16, 18, 36];
expect 0 <= 24 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 25, 36);
expect 24 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 24 <= r < 25 :: seqint0[r] != 36;
}
method {:test} Test20() {
var seqint0 : seq<int> := [17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 15, 0, 11, 0];
expect 0 <= 29 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 29, 29, 32);
expect 29 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 29 <= r < 29 :: seqint0[r] != 32;
}
method {:test} Test21() {
var seqint0 : seq<int> := [99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 94, 8];
expect 0 <= 14 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 15, 32);
expect 14 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 14 <= r < 15 :: seqint0[r] != 32;
}
method {:test} Test22() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 0, 95, 0, 0, 0, 0, 99, 96, 0, 30, 9];
expect 0 <= 14 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 15, 30);
expect 14 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 14 <= r < 15 :: seqint0[r] != 30;
}
method {:test} Test23() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 0, 0, 0, 0, 4, 7, 0, 0, 9, 0];
expect 0 <= 15 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 15, 15, 30);
expect 15 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 15 <= r < 15 :: seqint0[r] != 30;
}

// REPEAT 4 - TIME: 12.7052592 s

method {:test} Test24() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 22, 39, 38, 0, 37];
expect 0 <= 25 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 28, 38);
expect 25 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 25 <= r < 28 :: seqint0[r] != 38;
}
method {:test} Test25() {
var seqint0 : seq<int> := [41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 23, 0, 25, 38, 0, 39, 0];
expect 0 <= 25 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 26, 38);
expect 25 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 25 <= r < 26 :: seqint0[r] != 38;
}
method {:test} Test26() {
var seqint0 : seq<int> := [37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 22, 0, 0, 0, 24];
expect 0 <= 26 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 26, 26, 38);
expect 26 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 26 <= r < 26 :: seqint0[r] != 38;
}
method {:test} Test27() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 6, 14, 0];
expect 0 <= 17 <= 18 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 17, 18, 33);
expect 17 <= r0 < 18 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 18 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 17 <= r < 18 :: seqint0[r] != 33;
}
method {:test} Test28() {
var seqint0 : seq<int> := [17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 13, 0, 15, 31];
expect 0 <= 16 <= 17 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 16, 17, 31);
expect 16 <= r0 < 17 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 17 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 16 <= r < 17 :: seqint0[r] != 31;
}
method {:test} Test29() {
var seqint0 : seq<int> := [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 14, 0, 16, 12];
expect 0 <= 16 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 16, 16, 31);
expect 16 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 16 <= r < 16 :: seqint0[r] != 31;
}

// REPEAT 5 - TIME: 15.4096221 s

method {:test} Test30() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45];
expect 0 <= 21 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 27, 40);
expect 21 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 21 <= r < 27 :: seqint0[r] != 40;
}
method {:test} Test31() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 45];
expect 0 <= 21 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 27, 45);
expect 21 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 45;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 45;
expect r0 == -1 ==> forall r | 21 <= r < 27 :: seqint0[r] != 45;
}
method {:test} Test32() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 43];
expect 0 <= 27 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 27, 27, 40);
expect 27 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 27 <= r < 27 :: seqint0[r] != 40;
}
method {:test} Test33() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 195, 0, 0, 0, 0, 201, 197, 23, 199, 0, 0, 0, 0, 26];
expect 0 <= 18 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 18, 20, 38);
expect 18 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 18 <= r < 20 :: seqint0[r] != 38;
}
method {:test} Test34() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 20, 0, 0, 0, 22];
expect 0 <= 18 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 18, 24, 34);
expect 18 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 18 <= r < 24 :: seqint0[r] != 34;
}
method {:test} Test35() {
var seqint0 : seq<int> := [26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 21, 23];
expect 0 <= 19 <= 19 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 19, 19, 34);
expect 19 <= r0 < 19 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 19 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 19 <= r < 19 :: seqint0[r] != 34;
}

// REPEAT 6 - TIME: 18.2057827 s

method {:test} Test36() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 336, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46];
expect 0 <= 9 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 9, 10, 44);
expect 9 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 44;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 44;
expect r0 == -1 ==> forall r | 9 <= r < 10 :: seqint0[r] != 44;
}
method {:test} Test37() {
var seqint0 : seq<int> := [51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 49];
expect 0 <= 9 <= 18 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 9, 18, 46);
expect 9 <= r0 < 18 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 18 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 9 <= r < 18 :: seqint0[r] != 46;
}
method {:test} Test38() {
var seqint0 : seq<int> := [44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 16 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 16, 16, 44);
expect 16 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 44;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 44;
expect r0 == -1 ==> forall r | 16 <= r < 16 :: seqint0[r] != 44;
}
method {:test} Test39() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 255, 0, 0, 259];
expect 0 <= 20 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 20, 25, 35);
expect 20 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 20 <= r < 25 :: seqint0[r] != 35;
}
method {:test} Test40() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 0, 0, 38, 0, 35, 252, 40, 36, 0, 258];
expect 0 <= 20 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 20, 28, 36);
expect 20 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 20 <= r < 28 :: seqint0[r] != 36;
}
method {:test} Test41() {
var seqint0 : seq<int> := [35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 24, 0, 0, 0];
expect 0 <= 25 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 25, 25, 37);
expect 25 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 25 <= r < 25 :: seqint0[r] != 37;
}

// REPEAT 7 - TIME: 21.1185747 s

method {:test} Test42() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 53];
expect 0 <= 17 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 17, 20, 52);
expect 17 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 52;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 52;
expect r0 == -1 ==> forall r | 17 <= r < 20 :: seqint0[r] != 52;
}
method {:test} Test43() {
var seqint0 : seq<int> := [52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 17 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 17, 20, 48);
expect 17 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 48;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 48;
expect r0 == -1 ==> forall r | 17 <= r < 20 :: seqint0[r] != 48;
}
method {:test} Test44() {
var seqint0 : seq<int> := [52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 17 <= 17 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 17, 17, 48);
expect 17 <= r0 < 17 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 48;
expect r0 != -1 ==> forall r | r0 < r < 17 :: seqint0[r] != 48;
expect r0 == -1 ==> forall r | 17 <= r < 17 :: seqint0[r] != 48;
}
method {:test} Test45() {
var seqint0 : seq<int> := [317, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 311, 0, 315, 313, 316];
expect 0 <= 26 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 26, 29, 39);
expect 26 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 26 <= r < 29 :: seqint0[r] != 39;
}
method {:test} Test46() {
var seqint0 : seq<int> := [315, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 310, 0, 0, 0, 0, 0, 0, 312, 39, 314];
expect 0 <= 27 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 27, 29, 39);
expect 27 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 27 <= r < 29 :: seqint0[r] != 39;
}
method {:test} Test47() {
var seqint0 : seq<int> := [37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0];
expect 0 <= 29 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 29, 29, 42);
expect 29 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 42;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 42;
expect r0 == -1 ==> forall r | 29 <= r < 29 :: seqint0[r] != 42;
}

// REPEAT 8 - TIME: 24.9950679 s

method {:test} Test48() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 58];
expect 0 <= 15 <= 19 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 15, 19, 54);
expect 15 <= r0 < 19 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 54;
expect r0 != -1 ==> forall r | r0 < r < 19 :: seqint0[r] != 54;
expect r0 == -1 ==> forall r | 15 <= r < 19 :: seqint0[r] != 54;
}
method {:test} Test49() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54];
expect 0 <= 18 <= 19 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 18, 19, 54);
expect 18 <= r0 < 19 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 54;
expect r0 != -1 ==> forall r | r0 < r < 19 :: seqint0[r] != 54;
expect r0 == -1 ==> forall r | 18 <= r < 19 :: seqint0[r] != 54;
}
method {:test} Test50() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 15 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 15, 15, 57);
expect 15 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 57;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 57;
expect r0 == -1 ==> forall r | 15 <= r < 15 :: seqint0[r] != 57;
}
method {:test} Test51() {
var seqint0 : seq<int> := [405, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 28 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 28, 30, 41);
expect 28 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 41;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 41;
expect r0 == -1 ==> forall r | 28 <= r < 30 :: seqint0[r] != 41;
}
method {:test} Test52() {
var seqint0 : seq<int> := [405, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0];
expect 0 <= 28 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 28, 30, 43);
expect 28 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 43;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 43;
expect r0 == -1 ==> forall r | 28 <= r < 30 :: seqint0[r] != 43;
}
method {:test} Test53() {
var seqint0 : seq<int> := [33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 30 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 30, 30, 44);
expect 30 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 44;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 44;
expect r0 == -1 ==> forall r | 30 <= r < 30 :: seqint0[r] != 44;
}

// REPEAT 9 - TIME: 28.6862939 s

method {:test} Test54() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 0];
expect 0 <= 10 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 10, 14, 59);
expect 10 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 59;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 59;
expect r0 == -1 ==> forall r | 10 <= r < 14 :: seqint0[r] != 59;
}
method {:test} Test55() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0];
expect 0 <= 10 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 10, 14, 56);
expect 10 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 56;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 56;
expect r0 == -1 ==> forall r | 10 <= r < 14 :: seqint0[r] != 56;
}
method {:test} Test56() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 14 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 14, 14, 56);
expect 14 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 56;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 56;
expect r0 == -1 ==> forall r | 14 <= r < 14 :: seqint0[r] != 56;
}
method {:test} Test57() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 21 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 21, 26, 46);
expect 21 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 21 <= r < 26 :: seqint0[r] != 46;
}
method {:test} Test58() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0];
expect 0 <= 24 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 24, 26, 46);
expect 24 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 24 <= r < 26 :: seqint0[r] != 46;
}
method {:test} Test59() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 21 <= 21 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 21, 21, 45);
expect 21 <= r0 < 21 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 45;
expect r0 != -1 ==> forall r | r0 < r < 21 :: seqint0[r] != 45;
expect r0 == -1 ==> forall r | 21 <= r < 21 :: seqint0[r] != 45;
}

// REPEAT 10 - TIME: 33.0933856 s
