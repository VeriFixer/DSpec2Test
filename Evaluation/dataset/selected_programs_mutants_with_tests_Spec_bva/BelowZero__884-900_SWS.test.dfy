// BelowZero.dfy

function sum(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if |s| == 0 || n == 0 then
    0
  else
    s[0] + sum(s[1..], n - 1)
}

lemma sum_plus(s: seq<int>, i: nat)
  requires i < |s|
  ensures sum(s, i) + s[i] == sum(s, i + 1)
{
}

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
    t := t + ops[i];
    if t < 0 {
      result := true;
      return;
    }
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [8855, -7129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect 20 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
sum_plus(seqint0, 20);
expect sum(seqint0, 20) + seqint0[20] == sum(seqint0, 20 + 1);
}
method {:test} Test1() {
var seqint0 : seq<int> := [8855];
expect 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
sum_plus(seqint0, 0);
expect sum(seqint0, 0) + seqint0[0] == sum(seqint0, 0 + 1);
}
method {:test} Test2() {
var seqint0 : seq<int> := [8855, -560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect 20 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
sum_plus(seqint0, 20);
expect sum(seqint0, 20) + seqint0[20] == sum(seqint0, 20 + 1);
}
method {:test} Test3() {
var seqint0 : seq<int> := [2437, -7129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect 20 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
sum_plus(seqint0, 20);
expect sum(seqint0, 20) + seqint0[20] == sum(seqint0, 20 + 1);
}
method {:test} Test4() {
var seqint0 : seq<int> := [-1201, -7164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect 20 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
sum_plus(seqint0, 20);
expect sum(seqint0, 20) + seqint0[20] == sum(seqint0, 20 + 1);
}
method {:test} Test5() {
var seqint0 : seq<int> := [2437, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test6() {
var seqint0 : seq<int> := [-2438];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [7719, -8956];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [-2437, 640, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test12() {
var seqint0 : seq<int> := [];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test14() {
var seqint0 : seq<int> := [0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
method {:test} Test15() {
var seqint0 : seq<int> := [0, 0];
var r0 := BelowZero(seqint0);
expect r0 <==> exists n: nat :: n <= |seqint0| && sum(seqint0, n) < 0;
}
