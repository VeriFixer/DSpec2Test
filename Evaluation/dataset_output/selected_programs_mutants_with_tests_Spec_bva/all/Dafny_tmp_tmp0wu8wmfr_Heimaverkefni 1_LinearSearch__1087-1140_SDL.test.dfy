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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 22, 27);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != 27;
}
method {:test} Test1() {
var seqint0 : seq<int> := [26];
expect 0 <= 0 <= 1 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 1, 26);
expect 0 <= r0 < 1 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 1 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 0 <= r < 1 :: seqint0[r] != 26;
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0];
expect 0 <= 9 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 9, 10, 27);
expect 9 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 9 <= r < 10 :: seqint0[r] != 27;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 26];
expect 0 <= 0 <= 9 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 9, 26);
expect 0 <= r0 < 9 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 9 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 0 <= r < 9 :: seqint0[r] != 26;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -100];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 22, -100);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == -100;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != -100;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != -100;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 21, 22, 100);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 100;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 100;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != 100;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test12() {
var seqint0 : seq<int> := [0, 0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test14() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, -100);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == -100;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != -100;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != -100;
}
method {:test} Test15() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 0, 0, 100);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 100;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 100;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 100;
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 21, 22, 27);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != 27;
}
method {:test} Test20() {
var seqint0 : seq<int> := [26];
expect 0 <= 0 <= 1 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 1, 26);
expect 0 <= r0 < 1 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 1 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 0 <= r < 1 :: seqint0[r] != 26;
}
method {:test} Test21() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0];
expect 0 <= 9 <= 10 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 9, 10, 27);
expect 9 <= r0 < 10 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 27;
expect r0 != -1 ==> forall r | r0 < r < 10 :: seqint0[r] != 27;
expect r0 == -1 ==> forall r | 9 <= r < 10 :: seqint0[r] != 27;
}
method {:test} Test22() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 26];
expect 0 <= 0 <= 9 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 9, 26);
expect 0 <= r0 < 9 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 26;
expect r0 != -1 ==> forall r | r0 < r < 9 :: seqint0[r] != 26;
expect r0 == -1 ==> forall r | 0 <= r < 9 :: seqint0[r] != 26;
}
method {:test} Test23() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -100];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 21, 22, -100);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == -100;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != -100;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != -100;
}
method {:test} Test24() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100];
expect 0 <= 21 <= 22 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 21, 22, 100);
expect 21 <= r0 < 22 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 100;
expect r0 != -1 ==> forall r | r0 < r < 22 :: seqint0[r] != 100;
expect r0 == -1 ==> forall r | 21 <= r < 22 :: seqint0[r] != 100;
}
method {:test} Test28() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test29() {
var seqint0 : seq<int> := [];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test31() {
var seqint0 : seq<int> := [0, 0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 0, 0);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 0;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 0;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 0;
}
method {:test} Test33() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 0, -100);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == -100;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != -100;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != -100;
}
method {:test} Test34() {
var seqint0 : seq<int> := [0];
expect 0 <= 0 <= 0 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 0, 0, 100);
expect 0 <= r0 < 0 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 100;
expect r0 != -1 ==> forall r | r0 < r < 0 :: seqint0[r] != 100;
expect r0 == -1 ==> forall r | 0 <= r < 0 :: seqint0[r] != 100;
}

// REPEAT 1 - TIME: 41.3625872 s

method {:test} Test38() {
var seqint0 : seq<int> := [58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 61, 6, 0, 4];
expect 0 <= 22 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 22, 24, 25);
expect 22 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 25;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 25;
expect r0 == -1 ==> forall r | 22 <= r < 24 :: seqint0[r] != 25;
}
method {:test} Test39() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 22, 23, 24);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 24;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 24;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 24;
}
method {:test} Test40() {
var seqint0 : seq<int> := [58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 61, 6, 0, 4];
expect 0 <= 22 <= 24 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 22, 24, 25);
expect 22 <= r0 < 24 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 25;
expect r0 != -1 ==> forall r | r0 < r < 24 :: seqint0[r] != 25;
expect r0 == -1 ==> forall r | 22 <= r < 24 :: seqint0[r] != 25;
}
method {:test} Test41() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1];
expect 0 <= 22 <= 23 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 22, 23, 24);
expect 22 <= r0 < 23 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 24;
expect r0 != -1 ==> forall r | r0 < r < 23 :: seqint0[r] != 24;
expect r0 == -1 ==> forall r | 22 <= r < 23 :: seqint0[r] != 24;
}

// REPEAT 2 - TIME: 44.7633264 s

method {:test} Test42() {
var seqint0 : seq<int> := [122, 123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 9, 11];
expect 0 <= 23 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 25, 32);
expect 23 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 23 <= r < 25 :: seqint0[r] != 32;
}
method {:test} Test43() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 8, 0, 12];
expect 0 <= 23 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 23, 25, 33);
expect 23 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 23 <= r < 25 :: seqint0[r] != 33;
}
method {:test} Test44() {
var seqint0 : seq<int> := [122, 123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 9, 11];
expect 0 <= 23 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 23, 25, 32);
expect 23 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 32;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 32;
expect r0 == -1 ==> forall r | 23 <= r < 25 :: seqint0[r] != 32;
}
method {:test} Test45() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 8, 0, 12];
expect 0 <= 23 <= 25 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 23, 25, 33);
expect 23 <= r0 < 25 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 33;
expect r0 != -1 ==> forall r | r0 < r < 25 :: seqint0[r] != 33;
expect r0 == -1 ==> forall r | 23 <= r < 25 :: seqint0[r] != 33;
}

// REPEAT 3 - TIME: 48.3881297 s

method {:test} Test46() {
var seqint0 : seq<int> := [15, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 17, 0];
expect 0 <= 24 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 24, 28, 31);
expect 24 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 24 <= r < 28 :: seqint0[r] != 31;
}
method {:test} Test47() {
var seqint0 : seq<int> := [22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 16, 18, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 20];
expect 0 <= 28 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 28, 28, 35);
expect 28 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 28 <= r < 28 :: seqint0[r] != 35;
}
method {:test} Test48() {
var seqint0 : seq<int> := [15, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 17, 0];
expect 0 <= 24 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 24, 28, 31);
expect 24 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 31;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 31;
expect r0 == -1 ==> forall r | 24 <= r < 28 :: seqint0[r] != 31;
}
method {:test} Test49() {
var seqint0 : seq<int> := [22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 16, 18, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 20];
expect 0 <= 28 <= 28 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 28, 28, 35);
expect 28 <= r0 < 28 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 35;
expect r0 != -1 ==> forall r | r0 < r < 28 :: seqint0[r] != 35;
expect r0 == -1 ==> forall r | 28 <= r < 28 :: seqint0[r] != 35;
}

// REPEAT 4 - TIME: 52.1715796 s

method {:test} Test50() {
var seqint0 : seq<int> := [28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 221, 0, 0, 0, 0, 0, 0, 0, 0, 37];
expect 0 <= 29 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 29, 30, 37);
expect 29 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 29 <= r < 30 :: seqint0[r] != 37;
}
method {:test} Test51() {
var seqint0 : seq<int> := [23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19];
expect 0 <= 29 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 29, 29, 34);
expect 29 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 29 <= r < 29 :: seqint0[r] != 34;
}
method {:test} Test52() {
var seqint0 : seq<int> := [28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 221, 0, 0, 0, 0, 0, 0, 0, 0, 37];
expect 0 <= 29 <= 30 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 29, 30, 37);
expect 29 <= r0 < 30 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 37;
expect r0 != -1 ==> forall r | r0 < r < 30 :: seqint0[r] != 37;
expect r0 == -1 ==> forall r | 29 <= r < 30 :: seqint0[r] != 37;
}
method {:test} Test53() {
var seqint0 : seq<int> := [23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19];
expect 0 <= 29 <= 29 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 29, 29, 34);
expect 29 <= r0 < 29 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 34;
expect r0 != -1 ==> forall r | r0 < r < 29 :: seqint0[r] != 34;
expect r0 == -1 ==> forall r | 29 <= r < 29 :: seqint0[r] != 34;
}

// REPEAT 5 - TIME: 56.1114292 s

method {:test} Test54() {
var seqint0 : seq<int> := [44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 24, 34, 0, 0, 36, 39, 40, 42];
expect 0 <= 25 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 27, 39);
expect 25 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 25 <= r < 27 :: seqint0[r] != 39;
}
method {:test} Test55() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29];
expect 0 <= 25 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 25, 26, 39);
expect 25 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 25 <= r < 26 :: seqint0[r] != 39;
}
method {:test} Test56() {
var seqint0 : seq<int> := [44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 24, 34, 0, 0, 36, 39, 40, 42];
expect 0 <= 25 <= 27 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 25, 27, 39);
expect 25 <= r0 < 27 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 27 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 25 <= r < 27 :: seqint0[r] != 39;
}
method {:test} Test57() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29];
expect 0 <= 25 <= 26 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 25, 26, 39);
expect 25 <= r0 < 26 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 39;
expect r0 != -1 ==> forall r | r0 < r < 26 :: seqint0[r] != 39;
expect r0 == -1 ==> forall r | 25 <= r < 26 :: seqint0[r] != 39;
}

// REPEAT 6 - TIME: 60.6026787 s

method {:test} Test58() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 50, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 46, 48];
expect 0 <= 10 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 10, 11, 38);
expect 10 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 10 <= r < 11 :: seqint0[r] != 38;
}
method {:test} Test59() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0];
expect 0 <= 10 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 10, 11, 38);
expect 10 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 10 <= r < 11 :: seqint0[r] != 38;
}
method {:test} Test60() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 50, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 46, 48];
expect 0 <= 10 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 10, 11, 38);
expect 10 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 10 <= r < 11 :: seqint0[r] != 38;
}
method {:test} Test61() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0];
expect 0 <= 10 <= 11 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 10, 11, 38);
expect 10 <= r0 < 11 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 38;
expect r0 != -1 ==> forall r | r0 < r < 11 :: seqint0[r] != 38;
expect r0 == -1 ==> forall r | 10 <= r < 11 :: seqint0[r] != 38;
}

// REPEAT 7 - TIME: 65.0331117 s

method {:test} Test62() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 45, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 11 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 11, 12, 47);
expect 11 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 47;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 47;
expect r0 == -1 ==> forall r | 11 <= r < 12 :: seqint0[r] != 47;
}
method {:test} Test63() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41];
expect 0 <= 11 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 11, 12, 47);
expect 11 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 47;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 47;
expect r0 == -1 ==> forall r | 11 <= r < 12 :: seqint0[r] != 47;
}
method {:test} Test64() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 45, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 11 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 12, 47);
expect 11 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 47;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 47;
expect r0 == -1 ==> forall r | 11 <= r < 12 :: seqint0[r] != 47;
}
method {:test} Test65() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41];
expect 0 <= 11 <= 12 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 11, 12, 47);
expect 11 <= r0 < 12 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 47;
expect r0 != -1 ==> forall r | r0 < r < 12 :: seqint0[r] != 47;
expect r0 == -1 ==> forall r | 11 <= r < 12 :: seqint0[r] != 47;
}

// REPEAT 8 - TIME: 69.2419317 s

method {:test} Test66() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 12 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 12, 15, 52);
expect 12 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 52;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 52;
expect r0 == -1 ==> forall r | 12 <= r < 15 :: seqint0[r] != 52;
}
method {:test} Test67() {
var seqint0 : seq<int> := [49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 12 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 12, 13, 52);
expect 12 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 52;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 52;
expect r0 == -1 ==> forall r | 12 <= r < 13 :: seqint0[r] != 52;
}
method {:test} Test68() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 12 <= 15 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 12, 15, 52);
expect 12 <= r0 < 15 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 52;
expect r0 != -1 ==> forall r | r0 < r < 15 :: seqint0[r] != 52;
expect r0 == -1 ==> forall r | 12 <= r < 15 :: seqint0[r] != 52;
}
method {:test} Test69() {
var seqint0 : seq<int> := [49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 12 <= 13 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 12, 13, 52);
expect 12 <= r0 < 13 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 52;
expect r0 != -1 ==> forall r | r0 < r < 13 :: seqint0[r] != 52;
expect r0 == -1 ==> forall r | 12 <= r < 13 :: seqint0[r] != 52;
}

// REPEAT 9 - TIME: 73.623424 s

method {:test} Test70() {
var seqint0 : seq<int> := [436, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 13 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 13, 16, 55);
expect 13 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 55;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 55;
expect r0 == -1 ==> forall r | 13 <= r < 16 :: seqint0[r] != 55;
}
method {:test} Test71() {
var seqint0 : seq<int> := [55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 433, 438];
expect 0 <= 20 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchRecursive(seqint0, 20, 20, 53);
expect 20 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 53;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 53;
expect r0 == -1 ==> forall r | 20 <= r < 20 :: seqint0[r] != 53;
}
method {:test} Test72() {
var seqint0 : seq<int> := [436, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 <= 13 <= 16 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 13, 16, 55);
expect 13 <= r0 < 16 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 55;
expect r0 != -1 ==> forall r | r0 < r < 16 :: seqint0[r] != 55;
expect r0 == -1 ==> forall r | 13 <= r < 16 :: seqint0[r] != 55;
}
method {:test} Test73() {
var seqint0 : seq<int> := [55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 433, 438];
expect 0 <= 20 <= 20 <= |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SearchLoop(seqint0, 20, 20, 53);
expect 20 <= r0 < 20 || r0 == -1;
expect r0 != -1 ==> seqint0[r0] == 53;
expect r0 != -1 ==> forall r | r0 < r < 20 :: seqint0[r] != 53;
expect r0 == -1 ==> forall r | 20 <= r < 20 :: seqint0[r] != 53;
}

// REPEAT 10 - TIME: 78.0959074 s
