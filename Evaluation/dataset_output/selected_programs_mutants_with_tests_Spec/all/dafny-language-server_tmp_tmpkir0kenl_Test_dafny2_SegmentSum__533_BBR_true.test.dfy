// dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_SegmentSum.dfy

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then
    0
  else
    Sum(a, s, t - 1) + a[t - 1]
}

method {:testEntry} MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p, q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
  k, m := 0, 0;
  var s := 0;
  var n := 0;
  var c, t := 0, 0;
  while true
    invariant 0 <= c <= n <= |a| && t == Sum(a, c, n)
    invariant forall b :: 0 <= b <= n ==> Sum(a, b, n) <= Sum(a, c, n)
    invariant 0 <= k <= m <= n && s == Sum(a, k, m)
    invariant forall p, q :: 0 <= p <= q <= n ==> Sum(a, p, q) <= Sum(a, k, m)
  {
    t, n := t + a[n], n + 1;
    if t < 0 {
      c, t := n, 0;
    } else if s < t {
      k, m, s := c, n, t;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 1 - TIME: 3.451612 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 2 - TIME: 4.528944 s

method {:test} Test2() {
var seqint0 : seq<int> := [1, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 3 - TIME: 5.5482451 s

method {:test} Test3() {
var seqint0 : seq<int> := [4, 0, 2];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 4 - TIME: 6.8393401 s

method {:test} Test4() {
var seqint0 : seq<int> := [6, 0, 3];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 5 - TIME: 7.9401554 s

method {:test} Test5() {
var seqint0 : seq<int> := [12, 0, 10, 0, 0, 0, 0, 0, 0, 5, 0, 0, 8];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 6 - TIME: 9.0030763 s

method {:test} Test6() {
var seqint0 : seq<int> := [11, 7, 0, 0, 0, 14];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 7 - TIME: 10.0054102 s

method {:test} Test7() {
var seqint0 : seq<int> := [15, 9, 0, 0, 17];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 8 - TIME: 10.9216645 s

method {:test} Test8() {
var seqint0 : seq<int> := [20, 0, 13, 0, 0, 0, 0, 18, 22];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 9 - TIME: 11.7799944 s

method {:test} Test9() {
var seqint0 : seq<int> := [21, 16, 0, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 10 - TIME: 12.5590395 s
