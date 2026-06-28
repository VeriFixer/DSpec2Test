// dafny-synthesis_task_id_307.dfy

method {:testEntry} DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
  ensures |copy| == |s|
  ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
{
  var newSeq: seq<int> := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |newSeq| == i
    invariant forall k :: 0 <= k < i ==> newSeq[k] == s[k]
  {
    break;
    newSeq := newSeq + [s[i]];
  }
  return newSeq;
}


method {:test} Test0() {
var seqint0 : seq<int> := [];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}
method {:test} Test2() {
var seqint0 : seq<int> := [0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 1 - TIME: 8.8005423 s

method {:test} Test10() {
var seqint0 : seq<int> := [0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 2 - TIME: 9.6836259 s

method {:test} Test11() {
var seqint0 : seq<int> := [44, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 3 - TIME: 10.7578155 s

method {:test} Test12() {
var seqint0 : seq<int> := [55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 4 - TIME: 11.7909948 s

method {:test} Test13() {
var seqint0 : seq<int> := [66, 0, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 5 - TIME: 12.7128063 s

method {:test} Test14() {
var seqint0 : seq<int> := [71, 68, 0, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 6 - TIME: 13.6243717 s

method {:test} Test15() {
var seqint0 : seq<int> := [84, 77, 0, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 81];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 7 - TIME: 14.5424232 s

method {:test} Test16() {
var seqint0 : seq<int> := [96, 0, 0, 97, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 15.4959655 s

method {:test} Test17() {
var seqint0 : seq<int> := [100, 0, 0, 0, 103, 0, 0, 0, 101, 0, 0, 0, 0, 105];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 9 - TIME: 16.3615093 s

method {:test} Test18() {
var seqint0 : seq<int> := [126, 116, 0, 0, 120, 122];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 10 - TIME: 17.1721764 s
