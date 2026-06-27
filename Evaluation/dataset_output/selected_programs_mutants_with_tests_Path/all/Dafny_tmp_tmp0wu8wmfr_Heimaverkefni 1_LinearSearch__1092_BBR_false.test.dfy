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
  if false {
    k := -1;
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
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 28];
expect 0 <= 19 <= 21 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 19, 21, 26);
expect 19 <= r0 < 21 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 21 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 19 <= r < 21 :: seqint0[r] != 26;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 1 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 1, 0);
expect 0 <= r0 < 1 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 1 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 1 :: seqint0[r] != 0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 29];
expect 0 <= 8 <= 9 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 8, 9, 29);
expect 8 <= r0 < 9 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 9 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 8 <= r < 9 :: seqint0[r] != 29;
}

// REPEAT 1 - TIME: 17.1446894 s

method {:test} Test6() {
var seqint0 : seq<int> := [5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3];
expect 0 <= 22 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 22, 22, 30);
expect 22 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 22 <= r < 22 :: seqint0[r] != 30;
}
method {:test} Test7() {
var seqint0 : seq<int> := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30];
expect 0 <= 20 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 20, 22, 30);
expect 20 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 20 <= r < 22 :: seqint0[r] != 30;
}
method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 31];
expect 0 <= 20 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 20, 24, 30);
expect 20 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 20 <= r < 24 :: seqint0[r] != 30;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, 1, 0, 0, 0, 0, 0, 0, 0, 3];
expect 0 <= 10 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 10, 10, 25);
expect 10 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 25;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 25;
expect r0 == -1 ==> forall r | 10 <= r < 10 :: seqint0[r] != 25;
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 38, 0, 0, 0, 0, 0, 40, 0, 0];
expect 0 <= 9 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 9, 10, 30);
expect 9 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 30;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 30;
expect r0 == -1 ==> forall r | 9 <= r < 10 :: seqint0[r] != 30;
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 38, 0, 0, 0, 0, 0, 0, 0, 39, 0, 28];
expect 0 <= 9 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 9, 12, 28);
expect 9 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 28;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 28;
expect r0 == -1 ==> forall r | 9 <= r < 12 :: seqint0[r] != 28;
}

// REPEAT 2 - TIME: 30.5255526 s

method {:test} Test12() {
var seqint0 : seq<int> := [13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 11, 9, 0];
expect 0 <= 25 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 25, 29);
expect 25 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 25 <= r < 25 :: seqint0[r] != 29;
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32];
expect 0 <= 23 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 25, 32);
expect 23 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 23 <= r < 25 :: seqint0[r] != 32;
}
method {:test} Test14() {
var seqint0 : seq<int> := [0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101, 0, 0, 0, 0, 0, 0, 103, 0, 0, 0, 0, 0, 32, 102];
expect 0 <= 28 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 28, 30, 32);
expect 28 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 28 <= r < 30 :: seqint0[r] != 32;
}
method {:test} Test15() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0];
expect 0 <= 13 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 13, 13, 26);
expect 13 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 13 <= r < 13 :: seqint0[r] != 26;
}
method {:test} Test16() {
var seqint0 : seq<int> := [65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 0, 0];
expect 0 <= 11 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 13, 33);
expect 11 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 11 <= r < 13 :: seqint0[r] != 33;
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 63, 0, 0, 0, 0, 0, 0, 0, 27, 0, 5];
expect 0 <= 11 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 13, 27);
expect 11 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 11 <= r < 13 :: seqint0[r] != 27;
}

// REPEAT 3 - TIME: 47.4606215 s

method {:test} Test18() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 15, 17, 0, 0, 19, 0, 0, 12];
expect 0 <= 29 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 29, 29, 33);
expect 29 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 29 <= r < 29 :: seqint0[r] != 33;
}
method {:test} Test19() {
var seqint0 : seq<int> := [20, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 18, 0, 0, 16, 33];
expect 0 <= 26 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 26, 27, 33);
expect 26 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 26 <= r < 27 :: seqint0[r] != 33;
}
method {:test} Test20() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 181, 37, 14];
expect 0 <= 26 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 26, 29, 33);
expect 26 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 26 <= r < 29 :: seqint0[r] != 33;
}
method {:test} Test21() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 0, 0, 0, 0, 4, 7, 0, 9, 13, 15];
expect 0 <= 14 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 14, 34);
expect 14 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 14 <= r < 14 :: seqint0[r] != 34;
}
method {:test} Test22() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 7, 104, 0, 0];
expect 0 <= 14 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 15, 31);
expect 14 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 14 <= r < 15 :: seqint0[r] != 31;
}
method {:test} Test23() {
var seqint0 : seq<int> := [12, 0, 0, 109, 0, 0, 0, 0, 102, 103, 0, 0, 107, 105, 35, 106];
expect 0 <= 14 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 14, 15, 35);
expect 14 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 14 <= r < 15 :: seqint0[r] != 35;
}

// REPEAT 4 - TIME: 67.7259612 s

method {:test} Test24() {
var seqint0 : seq<int> := [42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 24, 35, 0, 38, 0, 0, 0, 29, 40];
expect 0 <= 10 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 10, 10, 34);
expect 10 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 10 <= r < 10 :: seqint0[r] != 34;
}
method {:test} Test25() {
var seqint0 : seq<int> := [40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 34, 36, 23, 38];
expect 0 <= 27 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 27, 28, 38);
expect 27 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 27 <= r < 28 :: seqint0[r] != 38;
}
method {:test} Test26() {
var seqint0 : seq<int> := [25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 38];
expect 0 <= 27 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 27, 28, 36);
expect 27 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 27 <= r < 28 :: seqint0[r] != 36;
}
method {:test} Test27() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 16, 18, 10];
expect 0 <= 16 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 16, 16, 32);
expect 16 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 16 <= r < 16 :: seqint0[r] != 32;
}
method {:test} Test28() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 0, 0, 0, 0, 0, 152, 0];
expect 0 <= 15 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 15, 16, 42);
expect 15 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 42;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 42;
expect r0 == -1 ==> forall r | 15 <= r < 16 :: seqint0[r] != 42;
}
method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 152];
expect 0 <= 15 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 15, 16, 32);
expect 15 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 15 <= r < 16 :: seqint0[r] != 32;
}

// REPEAT 5 - TIME: 87.0141992 s

method {:test} Test30() {
var seqint0 : seq<int> := [45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 43];
expect 0 <= 11 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 11, 11, 39);
expect 11 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 11 <= r < 11 :: seqint0[r] != 39;
}
method {:test} Test31() {
var seqint0 : seq<int> := [47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 43, 45];
expect 0 <= 24 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 26, 39);
expect 24 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 24 <= r < 26 :: seqint0[r] != 39;
}
method {:test} Test32() {
var seqint0 : seq<int> := [41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0];
expect 0 <= 24 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 26, 44);
expect 24 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 44;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 44;
expect r0 == -1 ==> forall r | 24 <= r < 26 :: seqint0[r] != 44;
}
method {:test} Test33() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
expect 0 <= 17 <= 17 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 17, 17, 41);
expect 17 <= r0 < 17 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 41;
expect r0 != -1 ==> forall r | r0 < r < 17 :: seqint0[r] != 41;
expect r0 == -1 ==> forall r | 17 <= r < 17 :: seqint0[r] != 41;
}
method {:test} Test34() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 0, 0, 173, 20, 17];
expect 0 <= 17 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 17, 26, 41);
expect 17 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 41;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 41;
expect r0 == -1 ==> forall r | 17 <= r < 26 :: seqint0[r] != 41;
}
method {:test} Test35() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 173, 36];
expect 0 <= 17 <= 18 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 17, 18, 36);
expect 17 <= r0 < 18 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 18 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 17 <= r < 18 :: seqint0[r] != 36;
}

// REPEAT 6 - TIME: 110.2466092 s

method {:test} Test36() {
var seqint0 : seq<int> := [46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 15 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 15, 15, 46);
expect 15 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 15 <= r < 15 :: seqint0[r] != 46;
}
method {:test} Test37() {
var seqint0 : seq<int> := [50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 48];
expect 0 <= 21 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 23, 46);
expect 21 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 21 <= r < 23 :: seqint0[r] != 46;
}
method {:test} Test38() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0];
expect 0 <= 21 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 23, 49);
expect 21 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 49;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 49;
expect r0 == -1 ==> forall r | 21 <= r < 23 :: seqint0[r] != 49;
}
method {:test} Test39() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 21];
expect 0 <= 27 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 27, 27, 37);
expect 27 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 27 <= r < 27 :: seqint0[r] != 37;
}
method {:test} Test40() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 18 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 18, 27, 46);
expect 18 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 46;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 46;
expect r0 == -1 ==> forall r | 18 <= r < 27 :: seqint0[r] != 46;
}
method {:test} Test41() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 22, 0, 26, 0, 0, 0, 0, 0, 24, 37];
expect 0 <= 18 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 18, 30, 37);
expect 18 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 18 <= r < 30 :: seqint0[r] != 37;
}

// REPEAT 7 - TIME: 136.9792107 s

method {:test} Test42() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 16 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 16, 16, 52);
expect 16 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 52;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 52;
expect r0 == -1 ==> forall r | 16 <= r < 16 :: seqint0[r] != 52;
}
method {:test} Test43() {
var seqint0 : seq<int> := [49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0];
expect 0 <= 16 <= 17 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 16, 17, 53);
expect 16 <= r0 < 17 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 53;
expect r0 != -1 ==> forall r | r0 < r < 17 :: seqint0[r] != 53;
expect r0 == -1 ==> forall r | 16 <= r < 17 :: seqint0[r] != 53;
}
method {:test} Test44() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 55, 0];
expect 0 <= 17 <= 19 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 17, 19, 54);
expect 17 <= r0 < 19 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 54;
expect r0 != -1 ==> forall r | r0 < r < 19 :: seqint0[r] != 54;
expect r0 == -1 ==> forall r | 17 <= r < 19 :: seqint0[r] != 54;
}
method {:test} Test45() {
var seqint0 : seq<int> := [33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 23, 0, 0, 0];
expect 0 <= 28 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 28, 28, 43);
expect 28 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 43;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 43;
expect r0 == -1 ==> forall r | 28 <= r < 28 :: seqint0[r] != 43;
}
method {:test} Test46() {
var seqint0 : seq<int> := [249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 244, 0, 0, 0, 241, 0, 242];
expect 0 <= 28 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 28, 29, 43);
expect 28 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 43;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 43;
expect r0 == -1 ==> forall r | 28 <= r < 29 :: seqint0[r] != 43;
}
method {:test} Test47() {
var seqint0 : seq<int> := [25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0];
expect 0 <= 28 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 28, 29, 47);
expect 28 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 47;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 47;
expect r0 == -1 ==> forall r | 28 <= r < 29 :: seqint0[r] != 47;
}

// REPEAT 8 - TIME: 181.0749889 s

method {:test} Test48() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 18 <= 18 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 18, 18, 56);
expect 18 <= r0 < 18 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 56;
expect r0 != -1 ==> forall r | r0 < r < 18 :: seqint0[r] != 56;
expect r0 == -1 ==> forall r | 18 <= r < 18 :: seqint0[r] != 56;
}
method {:test} Test49() {
var seqint0 : seq<int> := [52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 18 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 18, 20, 58);
expect 18 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 58;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 58;
expect r0 == -1 ==> forall r | 18 <= r < 20 :: seqint0[r] != 58;
}
method {:test} Test50() {
var seqint0 : seq<int> := [541, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 18 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 18, 20, 58);
expect 18 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 58;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 58;
expect r0 == -1 ==> forall r | 18 <= r < 20 :: seqint0[r] != 58;
}
method {:test} Test51() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 19 <= 19 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 19, 19, 48);
expect 19 <= r0 < 19 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 48;
expect r0 != -1 ==> forall r | r0 < r < 19 :: seqint0[r] != 48;
expect r0 == -1 ==> forall r | 19 <= r < 19 :: seqint0[r] != 48;
}
method {:test} Test52() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 19 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 19, 20, 49);
expect 19 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 49;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 49;
expect r0 == -1 ==> forall r | 19 <= r < 20 :: seqint0[r] != 49;
}
method {:test} Test53() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 21, 22, 49);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 49;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 49;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != 49;
}

// REPEAT 9 - TIME: 231.5914862 s

method {:test} Test54() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 12 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 12, 12, 60);
expect 12 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 60;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 60;
expect r0 == -1 ==> forall r | 12 <= r < 12 :: seqint0[r] != 60;
}
method {:test} Test55() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0];
expect 0 <= 13 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 13, 14, 57);
expect 13 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 57;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 57;
expect r0 == -1 ==> forall r | 13 <= r < 14 :: seqint0[r] != 57;
}
method {:test} Test56() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 62, 0, 0, 0, 0];
expect 0 <= 12 <= 14 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 12, 14, 61);
expect 12 <= r0 < 14 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 61;
expect r0 != -1 ==> forall r | r0 < r < 14 :: seqint0[r] != 61;
expect r0 == -1 ==> forall r | 12 <= r < 14 :: seqint0[r] != 61;
}
method {:test} Test57() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 23 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 23, 23, 50);
expect 23 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 50;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 50;
expect r0 == -1 ==> forall r | 23 <= r < 23 :: seqint0[r] != 50;
}
method {:test} Test58() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 22, 23, 44);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 44;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 44;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 44;
}
method {:test} Test59() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 22, 23, 45);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 45;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 45;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 45;
}

// REPEAT 10 - TIME: 294.5947426 s
