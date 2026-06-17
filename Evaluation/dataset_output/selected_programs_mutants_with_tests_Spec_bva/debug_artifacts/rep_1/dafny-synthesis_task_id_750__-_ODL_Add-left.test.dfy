// dafny-synthesis_task_id_750.dfy

method {:testEntry} AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
  ensures |r| == |l| + 1
  ensures r[|r| - 1] == t
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
  r := [t];
}

method {:test} Test0() {
var int0 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0];
var int1 : (int, int) := (3,2);
var r0 := AddTupleToList(seqint0, int1);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int1;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}
method {:test} Test1() {
var seqint0 : seq<(int, int)> := [];
var int0 : (int, int) := (2,3);
var r0 := AddTupleToList(seqint0, int0);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int0;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}
method {:test} Test2() {
var int0 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0];
var int1 : (int, int) := (2,3);
var r0 := AddTupleToList(seqint0, int1);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int1;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}
method {:test} Test3() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var int5 : (int, int) := (0,0);
var int6 : (int, int) := (0,0);
var int7 : (int, int) := (0,0);
var int8 : (int, int) := (0,0);
var int9 : (int, int) := (0,0);
var int10 : (int, int) := (0,0);
var int11 : (int, int) := (0,0);
var int12 : (int, int) := (0,0);
var int13 : (int, int) := (0,0);
var int14 : (int, int) := (0,0);
var int15 : (int, int) := (0,0);
var int16 : (int, int) := (0,0);
var int17 : (int, int) := (0,0);
var int18 : (int, int) := (0,0);
var int19 : (int, int) := (0,0);
var int20 : (int, int) := (0,0);
var int21 : (int, int) := (0,0);
var int22 : (int, int) := (0,0);
var int23 : (int, int) := (0,0);
var int24 : (int, int) := (0,0);
var int25 : (int, int) := (0,0);
var int26 : (int, int) := (0,0);
var int27 : (int, int) := (0,0);
var int28 : (int, int) := (0,0);
var int29 : (int, int) := (0,0);
var int30 : (int, int) := (0,0);
var int31 : (int, int) := (0,0);
var int32 : (int, int) := (0,0);
var int33 : (int, int) := (0,0);
var int34 : (int, int) := (0,0);
var int35 : (int, int) := (0,0);
var int36 : (int, int) := (0,0);
var int37 : (int, int) := (0,0);
var int38 : (int, int) := (0,0);
var int39 : (int, int) := (0,0);
var int40 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40];
var int41 : (int, int) := (2,3);
var r0 := AddTupleToList(seqint0, int41);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int41;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 1 - TIME: 6.3662541 s
