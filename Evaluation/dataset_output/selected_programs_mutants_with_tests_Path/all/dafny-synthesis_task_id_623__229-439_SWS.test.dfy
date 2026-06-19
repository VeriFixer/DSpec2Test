// dafny-synthesis_task_id_623.dfy

method {:testEntry} PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
  requires n >= 0
  ensures |result| == |l|
  ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == Power(l[k], n)
  {
    result := result + [Power(l[i], n)];
  }
  result := [];
}

function Power(base: int, exponent: int): int
  requires exponent >= 0
{
  if exponent == 0 then
    1
  else
    base * Power(base, exponent - 1)
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 0);
}

// REPEAT 1 - TIME: 13.9169885 s

method {:test} Test1() {
var seqint0 : seq<int> := [8855];
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1);
}

// REPEAT 2 - TIME: 23.6618825 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2);
}

// REPEAT 3 - TIME: 35.1749938 s

method {:test} Test3() {
var seqint0 : seq<int> := [];
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 3);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 3);
}

// REPEAT 4 - TIME: 47.1594244 s

method {:test} Test4() {
var seqint0 : seq<int> := [1, 0, 2331];
expect 1577 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1577);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1577);
}

// REPEAT 5 - TIME: 58.6425659 s

method {:test} Test5() {
var seqint0 : seq<int> := [977, 0, 1888];
expect 1578 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1578);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1578);
}

// REPEAT 6 - TIME: 68.3659954 s

method {:test} Test6() {
var seqint0 : seq<int> := [1888, 0, 0, 0, 0, 0, 0];
expect 1579 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1579);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1579);
}

// REPEAT 7 - TIME: 78.0412869 s

method {:test} Test7() {
var seqint0 : seq<int> := [1888, 0, 0, 0];
expect 1580 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1580);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1580);
}

// REPEAT 8 - TIME: 88.8063562 s

method {:test} Test8() {
var seqint0 : seq<int> := [8221, 0, 0, 0];
expect 1581 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1581);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1581);
}

// REPEAT 9 - TIME: 103.3182464 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 1888, 0];
expect 1582 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1582);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1582);
}

// REPEAT 10 - TIME: 118.4752478 s
