// dafny-synthesis_task_id_290.dfy

method {:testEntry} MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
  requires |lists| > 0
  ensures forall l :: l in lists ==> |l| <= |maxList|
  ensures maxList in lists
{
  maxList := lists[0];
  for i := 1 to |lists|
    invariant 1 <= i <= |lists|
    invariant forall l :: l in lists[..i] ==> |l| <= |maxList|
    invariant maxList in lists[..i]
  {
  }
}

method {:test} Test5() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [0, 0, 0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 6 - TIME: 7.6467461 s
