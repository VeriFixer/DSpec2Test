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
    sum_plus(ops, i);
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
var seqint0 : seq<int> := [];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [2436, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [-10092, 8855, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [5, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test6() {
var seqint0 : seq<int> := [-7758, 7719];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 2, 0, 6];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test8() {
var seqint0 : seq<int> := [-17221, 8365, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 9, 0, 13, 0, 0, 0, 15];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [-1797, 1796, 0, 0, 0, 0, 0, 12, 16, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 16, 7, 18];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
