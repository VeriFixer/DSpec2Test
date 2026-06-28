// dafny-synthesis_task_id_142.dfy

method {:testEntry} CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>)
    returns (count: int)
  requires |a| == |b| && |b| == |c|
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{
  var identical := set i: int | 0 <= i < |a| && a[i] < b[i] && b[i] == c[i];
  count := |identical|;
}

method {:test} Test40() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 814];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 814];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 814];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}
method {:test} Test41() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 815];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 815];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 815];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}
method {:test} Test42() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 815];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 815];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 815];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}
method {:test} Test43() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 814];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 814];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 814];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}
method {:test} Test44() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 813, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 813, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 813, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 9 - TIME: 168.5716468 s
