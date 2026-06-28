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
  if j >= i {
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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 22, 27);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != 27;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 21, 22, 27);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != 27;
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

// REPEAT 1 - TIME: 5.3585697 s

method {:test} Test4() {
var seqint0 : seq<int> := [45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 22, 23, 24);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 24;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 24;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 24;
}
method {:test} Test5() {
var seqint0 : seq<int> := [2, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 22, 23, 26);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 26;
}
method {:test} Test6() {
var seqint0 : seq<int> := [45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 22, 23, 24);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 24;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 24;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 24;
}
method {:test} Test7() {
var seqint0 : seq<int> := [2, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 22, 23, 26);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 26;
}

// REPEAT 2 - TIME: 8.5508619 s

method {:test} Test8() {
var seqint0 : seq<int> := [100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 6, 0, 4];
expect 0 <= 23 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 26, 25);
expect 23 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 25;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 25;
expect r0 == -1 ==> forall r | 23 <= r < 26 :: seqint0[r] != 25;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, 93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 95];
expect 0 <= 23 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 24, 29);
expect 23 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 23 <= r < 24 :: seqint0[r] != 29;
}
method {:test} Test10() {
var seqint0 : seq<int> := [100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 6, 0, 4];
expect 0 <= 23 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 23, 26, 25);
expect 23 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 25;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 25;
expect r0 == -1 ==> forall r | 23 <= r < 26 :: seqint0[r] != 25;
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 95];
expect 0 <= 23 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 23, 24, 29);
expect 23 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 29;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 29;
expect r0 == -1 ==> forall r | 23 <= r < 24 :: seqint0[r] != 29;
}

// REPEAT 3 - TIME: 10.9092582 s

method {:test} Test12() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 3];
expect 0 <= 24 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 27, 32);
expect 24 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 24 <= r < 27 :: seqint0[r] != 32;
}
method {:test} Test13() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
expect 0 <= 24 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 27, 32);
expect 24 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 24 <= r < 27 :: seqint0[r] != 32;
}
method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 3];
expect 0 <= 24 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 24, 27, 32);
expect 24 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 24 <= r < 27 :: seqint0[r] != 32;
}
method {:test} Test15() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
expect 0 <= 24 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 24, 27, 32);
expect 24 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 24 <= r < 27 :: seqint0[r] != 32;
}

// REPEAT 4 - TIME: 13.0742092 s

method {:test} Test16() {
var seqint0 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 10, 33, 0, 0];
expect 0 <= 25 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 28, 33);
expect 25 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 25 <= r < 28 :: seqint0[r] != 33;
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 9];
expect 0 <= 25 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 28, 31);
expect 25 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 25 <= r < 28 :: seqint0[r] != 31;
}
method {:test} Test18() {
var seqint0 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 10, 33, 0, 0];
expect 0 <= 25 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 25, 28, 33);
expect 25 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 25 <= r < 28 :: seqint0[r] != 33;
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 9];
expect 0 <= 25 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 25, 28, 31);
expect 25 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 25 <= r < 28 :: seqint0[r] != 31;
}

// REPEAT 5 - TIME: 15.0148752 s

method {:test} Test20() {
var seqint0 : seq<int> := [0, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 220, 222, 0, 0, 36, 0, 224, 0];
expect 0 <= 26 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 26, 29, 36);
expect 26 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 26 <= r < 29 :: seqint0[r] != 36;
}
method {:test} Test21() {
var seqint0 : seq<int> := [222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 220, 0, 0, 221];
expect 0 <= 26 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 26, 29, 36);
expect 26 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 26 <= r < 29 :: seqint0[r] != 36;
}
method {:test} Test22() {
var seqint0 : seq<int> := [0, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 220, 222, 0, 0, 36, 0, 224, 0];
expect 0 <= 26 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 26, 29, 36);
expect 26 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 26 <= r < 29 :: seqint0[r] != 36;
}
method {:test} Test23() {
var seqint0 : seq<int> := [222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 220, 0, 0, 221];
expect 0 <= 26 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 26, 29, 36);
expect 26 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 36;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 36;
expect r0 == -1 ==> forall r | 26 <= r < 29 :: seqint0[r] != 36;
}

// REPEAT 6 - TIME: 17.0179032 s

method {:test} Test24() {
var seqint0 : seq<int> := [293, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 37];
expect 0 <= 27 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 27, 30, 37);
expect 27 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 27 <= r < 30 :: seqint0[r] != 37;
}
method {:test} Test25() {
var seqint0 : seq<int> := [292, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 30 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 30, 30, 34);
expect 30 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 30 <= r < 30 :: seqint0[r] != 34;
}
method {:test} Test26() {
var seqint0 : seq<int> := [293, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 37];
expect 0 <= 27 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 27, 30, 37);
expect 27 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 27 <= r < 30 :: seqint0[r] != 37;
}
method {:test} Test27() {
var seqint0 : seq<int> := [292, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 30 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 30, 30, 34);
expect 30 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 30 <= r < 30 :: seqint0[r] != 34;
}

// REPEAT 7 - TIME: 19.461966 s

method {:test} Test28() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0];
expect 0 <= 1 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 1, 25, 39);
expect 1 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 1 <= r < 25 :: seqint0[r] != 39;
}
method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0];
expect 0 <= 1 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 1, 25, 39);
expect 1 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 1 <= r < 25 :: seqint0[r] != 39;
}
method {:test} Test30() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0];
expect 0 <= 1 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 1, 25, 39);
expect 1 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 1 <= r < 25 :: seqint0[r] != 39;
}
method {:test} Test31() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0];
expect 0 <= 1 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 1, 25, 39);
expect 1 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 1 <= r < 25 :: seqint0[r] != 39;
}

// REPEAT 8 - TIME: 21.5250715 s

method {:test} Test32() {
var seqint0 : seq<int> := [0, 0, 40, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 2 <= 3 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 2, 3, 40);
expect 2 <= r0 < 3 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 3 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 2 <= r < 3 :: seqint0[r] != 40;
}
method {:test} Test33() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 2 <= 2 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 2, 2, 40);
expect 2 <= r0 < 2 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 2 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 2 <= r < 2 :: seqint0[r] != 40;
}
method {:test} Test34() {
var seqint0 : seq<int> := [0, 0, 40, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 2 <= 3 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 2, 3, 40);
expect 2 <= r0 < 3 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 3 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 2 <= r < 3 :: seqint0[r] != 40;
}
method {:test} Test35() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 2 <= 2 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 2, 2, 40);
expect 2 <= r0 < 2 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 40;
expect r0 != -1 ==> forall r | r0 < r < 2 :: seqint0[r] != 40;
expect r0 == -1 ==> forall r | 2 <= r < 2 :: seqint0[r] != 40;
}

// REPEAT 9 - TIME: 24.0159005 s

method {:test} Test36() {
var seqint0 : seq<int> := [0, 0, 0, 0, 420, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 20];
expect 0 <= 3 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 3, 13, 35);
expect 3 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 3 <= r < 13 :: seqint0[r] != 35;
}
method {:test} Test37() {
var seqint0 : seq<int> := [0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 3 <= 4 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 3, 4, 35);
expect 3 <= r0 < 4 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 4 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 3 <= r < 4 :: seqint0[r] != 35;
}
method {:test} Test38() {
var seqint0 : seq<int> := [0, 0, 0, 0, 420, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 20];
expect 0 <= 3 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 3, 13, 35);
expect 3 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 3 <= r < 13 :: seqint0[r] != 35;
}
method {:test} Test39() {
var seqint0 : seq<int> := [0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 3 <= 4 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 3, 4, 35);
expect 3 <= r0 < 4 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 4 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 3 <= r < 4 :: seqint0[r] != 35;
}

// REPEAT 10 - TIME: 26.4051174 s
