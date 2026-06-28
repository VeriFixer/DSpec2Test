// dafny-synthesis_task_id_142.dfy

method {:testEntry} CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>)
    returns (count: int)
  requires |a| == |b| && |b| == |c|
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{
  var identical := set i: int | 0 <= i < |a| && a[i] != b[i] && b[i] == c[i];
  count := |identical|;
}


method {:test} Test0() {
var seqint0 : seq<int> := [27];
var seqint1 : seq<int> := [27];
var seqint2 : seq<int> := [27];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.6013518 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.7617145 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 8, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 3, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.9131606 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 93, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 93, 0, 0];
var seqint2 : seq<int> := [4, 0, 0, 0, 0, 93, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 4 - TIME: 6.027758 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 15];
var seqint1 : seq<int> := [17, 0, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 13];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 5 - TIME: 7.1230095 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 12, 0, 26, 22];
var seqint1 : seq<int> := [29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 0, 7, 24, 0];
var seqint2 : seq<int> := [31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 0, 20, 0, 18];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.2506858 s

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 35, 30, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 33, 0, 39];
var seqint2 : seq<int> := [0, 10, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 37, 0, 0, 41];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 7 - TIME: 9.3558397 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 252, 47, 0, 0, 40, 43];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 0, 23, 0, 0, 0];
var seqint2 : seq<int> := [0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 252, 0, 0, 0, 0, 36];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 8 - TIME: 10.3614252 s

method {:test} Test8() {
var seqint0 : seq<int> := [38, 304];
var seqint1 : seq<int> := [0, 304];
var seqint2 : seq<int> := [28, 304];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 9 - TIME: 11.2538657 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 311, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 52];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 311, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 311, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 49];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 10 - TIME: 12.3394757 s
