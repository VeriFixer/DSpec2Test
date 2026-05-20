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
    t := t + ops[i];
    if t < 0 {
      result := true;
      return;
    }
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [2437, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [-2438];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [7719, -8956];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [-2437, 640, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test15() {
var seqint0 : seq<int> := [-4234, 1796, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test16() {
var seqint0 : seq<int> := [3, 1, 5];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test17() {
var seqint0 : seq<int> := [-17221, 8365, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 10];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test18() {
var seqint0 : seq<int> := [10, 6, 8, 2];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test19() {
var seqint0 : seq<int> := [-4079, 2282, 0, 0, 0, 0, 0, 9, 16, 0, 14, 0, 12, 0, 0, 0, 18];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test20() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 14, 0, 12, 9, 0, 0, 0, 4, 18];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test21() {
var seqint0 : seq<int> := [-17220, 8364, 0, 13, 0, 0, 0, 0, 0, 17];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test22() {
var seqint0 : seq<int> := [26, 0, 0, 0, 0, 0, 0, 7, 0, 17, 13, 0, 0, 0, 0, 20, 24, 22];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
