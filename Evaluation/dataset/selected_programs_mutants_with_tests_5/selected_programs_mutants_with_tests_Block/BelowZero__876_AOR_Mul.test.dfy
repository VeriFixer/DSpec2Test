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
    t := t * ops[i];
    sum_plus(ops, i);
    if t < 0 {
      result := true;
      return;
    }
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [2437, -4719, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7720];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [-16575, 8210, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7720];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [-8855, 490, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8856, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [-16575, 8210, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7720, 0, 0, 0, 0, 4];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [-1796, -486, 0, 0, 0, 0, 0, 0, 0, -1797, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat {:trigger sum(seqint0, n)} :: n <= |seqint0| && sum(seqint0, n) < 0;
}
