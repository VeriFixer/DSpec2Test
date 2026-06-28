// dafny-synthesis_task_id_142.dfy

method {:testEntry} CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>)
    returns (count: int)
  requires |a| == |b| && |b| == |c|
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{
  var identical := set i: int | 0 == i < |a| && a[i] == b[i] && b[i] == c[i];
  count := |identical|;
}

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 35, 30, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 33, 0, 39];
var seqint2 : seq<int> := [0, 10, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 37, 0, 0, 41];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 7 - TIME: 9.3558397 s
