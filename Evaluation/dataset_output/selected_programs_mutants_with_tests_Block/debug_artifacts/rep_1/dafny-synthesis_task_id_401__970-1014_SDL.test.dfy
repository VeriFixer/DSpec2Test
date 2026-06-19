// dafny-synthesis_task_id_401.dfy

method {:testEntry} IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| > 0 && |b| > 0
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
  ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |a[k]|
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
  {
    var subResult := [];
    for j := 0 to |a[i]|
      invariant 0 <= j <= |a[i]|
      invariant |subResult| == j
      invariant forall k :: 0 <= k < j ==> subResult[k] == a[i][k] + b[i][k]
    {
    }
    result := result + [subResult];
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0];
var seqint1 : seq<int> := [0];
var seqseqint1 : seq<seq<int>> := [seqint1];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 1 - TIME: 2.7251622 s
