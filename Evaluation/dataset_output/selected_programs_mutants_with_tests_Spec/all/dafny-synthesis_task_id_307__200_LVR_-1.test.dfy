// dafny-synthesis_task_id_307.dfy

method {:testEntry} DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
  ensures |copy| == |s|
  ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
{
  var newSeq: seq<int> := [];
  for i := -1 to |s|
    invariant 0 <= i <= |s|
    invariant |newSeq| == i
    invariant forall k :: 0 <= k < i ==> newSeq[k] == s[k]
  {
    newSeq := newSeq + [s[i]];
  }
  return newSeq;
}


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

// REPEAT 1 - TIME: 2.7608267 s

method {:test} Test1() {
var seqint0 : seq<int> := [0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 2 - TIME: 3.7120089 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 3 - TIME: 4.6284203 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 29, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 4 - TIME: 5.5338626 s

method {:test} Test4() {
var seqint0 : seq<int> := [33, 31];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 5 - TIME: 6.3475497 s

method {:test} Test5() {
var seqint0 : seq<int> := [35, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 6 - TIME: 7.1844038 s

method {:test} Test6() {
var seqint0 : seq<int> := [39, 37, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 7 - TIME: 7.9268432 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 42, 0, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 8.5683911 s

method {:test} Test8() {
var seqint0 : seq<int> := [46, 0, 0, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 9 - TIME: 9.1729708 s

method {:test} Test9() {
var seqint0 : seq<int> := [53, 50, 51];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 10 - TIME: 9.7775164 s
