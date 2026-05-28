// BelowZero.dfy

function sum(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if |s| == 0 || n == 0 then
    0
  else
    s[0] + sum(s[1..], n - 1)
}

lemma {:axiom} sum_plus(s: seq<int>, i: nat)
  requires i < |s|
  ensures sum(s, i) + s[i] == sum(s, i + 1)

method {:testEntry} BelowZero(ops: seq<int>) returns (result: bool)
  ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
  result := false;
  var t := 0;
  for i := 0 to |ops|
    invariant t == sum(ops, i)
    invariant forall n: nat :: n <= i ==> sum(ops, n) >= 0
  {
    t := t;
    sum_plus(ops, i);
    if t < 0 {
      result := true;
      return;
    }
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [2282];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [8855, -17220, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7720];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [8855, -17220, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [-16575, 8210, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7720];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [8365];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [-2283, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test6() {
var seqint0 : seq<int> := [8366];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [-1796, -486, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1797, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test8() {
var seqint0 : seq<int> := [9508];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [-8365, 7916, 0, 0, 0, 0, 0, -8366, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 11];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [8365, -2282, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 12, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 4, 0, 0, 0, 14, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [-449, -5404, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 13, 10, 0, 0, 0, 0, -450, 0, 0, 0, 15];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
