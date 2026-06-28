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
    t, n := t * a[n], n + 1;
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
method {:test} Test1() {
var seqint0 : seq<int> := [];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 1 - TIME: 11.2549703 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 1, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 2 - TIME: 12.2765325 s

method {:test} Test10() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 6];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 3 - TIME: 13.4276172 s

method {:test} Test11() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 7];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 4 - TIME: 14.5690595 s

method {:test} Test12() {
var seqint0 : seq<int> := [11, 0, 5, 0, 0, 9];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 5 - TIME: 15.8792441 s

method {:test} Test13() {
var seqint0 : seq<int> := [8, 0, 0, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 6 - TIME: 17.1392571 s

method {:test} Test14() {
var seqint0 : seq<int> := [13, 0, 0, 10, 0];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 7 - TIME: 18.3564112 s

method {:test} Test15() {
var seqint0 : seq<int> := [17, 0, 12, 15];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 8 - TIME: 19.4844309 s

method {:test} Test16() {
var seqint0 : seq<int> := [14, 0, 0, 0, 22, 18, 20];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 9 - TIME: 20.518855 s

method {:test} Test17() {
var seqint0 : seq<int> := [26, 16, 0, 0, 21, 24];
var r0, r1 := MaxSegSum(seqint0);
expect 0 <= r0 <= r1 <= |seqint0|;
expect forall p, q :: 0 <= p <= q <= |seqint0| ==> Sum(seqint0, p, q) <= Sum(seqint0, r0, r1);
}

// REPEAT 10 - TIME: 21.3438825 s
