// dafny-synthesis_task_id_142.dfy

method {:testEntry} CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>)
    returns (count: int)
  requires |a| == |b| && |b| == |c|
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{
  var identical := set i: int | 0 <= i < |a| && a[i] > b[i] && b[i] == c[i];
  count := |identical|;
}

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 349, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 28];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 349, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 349, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.4495875 s
