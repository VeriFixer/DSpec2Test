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
