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
  while n < |a|
    invariant 0 <= c <= n <= |a| && t == Sum(a, c, n)
    invariant forall b :: 0 <= b <= n ==> Sum(a, b, n) <= Sum(a, c, n)
    invariant 0 <= k <= m <= n && s == Sum(a, k, m)
    invariant forall p, q :: 0 <= p <= q <= n ==> Sum(a, p, q) <= Sum(a, k, m)
  {
    if t < 0 {
      c, t := n, 0;
    } else if s < t {
      k, m, s := c, n, t;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, -10091, 1236, 1];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2437, 2437, -1];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 1 - TIME: 3.5105057 s

method {:test} Test2() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 8855, 7720];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test3() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 8855, -1237];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 2 - TIME: 5.2845867 s

method {:test} Test4() {
var seqint0 : seq<int> := [-1236, 1236, 7720];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test5() {
var seqint0 : seq<int> := [8, 8365, 8855, -1237, 6];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 3 - TIME: 6.7356379 s

method {:test} Test6() {
var seqint0 : seq<int> := [7, 8365, 8855, 7720];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test7() {
var seqint0 : seq<int> := [7, 8365, 8855, -1237];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 4 - TIME: 8.2295665 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 609, 8855, 1237, 0, 0, 0, 0, 0, 0, 9, 0, 11, 0, 13, 0, 15];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test9() {
var seqint0 : seq<int> := [9, 8365, 8855, -7720];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 5 - TIME: 10.0104078 s

method {:test} Test10() {
var seqint0 : seq<int> := [-609, 609, 8856];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test11() {
var seqint0 : seq<int> := [-450, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 6 - TIME: 11.6320439 s

method {:test} Test12() {
var seqint0 : seq<int> := [-608, 608, 5854];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 2282, 8855, -7720, 10, 0, 0, 0, 0, 0, 0, 0, 17, 0, 14, 0, 0, 0, 19];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 7 - TIME: 12.89744 s

method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 12, 0, 0, 0, 0, 0, 21, 609, 2282, 1237, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test15() {
var seqint0 : seq<int> := [-5854];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 8 - TIME: 14.2027107 s

method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 449, 8365, 1237, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2282, 1796, -1237, 0, 22, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 9 - TIME: 15.4737295 s

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 28, 0, 0, 0, 0, 0, 0, 609, 2282, 1237, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test19() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 8365, 8855, -1237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 10 - TIME: 16.7966649 s
