// dafny-synthesis_task_id_750.dfy

method {:testEntry} AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
  ensures |r| == |l| + 1
  ensures r[|r| - 1] == t
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
  r := l + [];
}


method {:test} Test0() {
var seqint0 : seq<(int, int)> := [];
var int0 : (int, int) := (2,3);
var r0 := AddTupleToList(seqint0, int0);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int0;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 1 - TIME: 2.4183976 s

method {:test} Test1() {
var int0 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0];
var int1 : (int, int) := (5,4);
var r0 := AddTupleToList(seqint0, int1);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int1;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 2 - TIME: 3.2156715 s

method {:test} Test2() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1];
var int2 : (int, int) := (7,6);
var r0 := AddTupleToList(seqint0, int2);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int2;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 3 - TIME: 3.9871648 s

method {:test} Test3() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2];
var int3 : (int, int) := (9,8);
var r0 := AddTupleToList(seqint0, int3);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int3;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 4 - TIME: 4.8320523 s

method {:test} Test4() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3];
var int4 : (int, int) := (11,10);
var r0 := AddTupleToList(seqint0, int4);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int4;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 5 - TIME: 5.6751252 s

method {:test} Test5() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4];
var int5 : (int, int) := (13,12);
var r0 := AddTupleToList(seqint0, int5);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int5;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 6 - TIME: 6.5360854 s

method {:test} Test6() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var int5 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5];
var int6 : (int, int) := (15,14);
var r0 := AddTupleToList(seqint0, int6);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int6;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 7 - TIME: 7.3454581 s

method {:test} Test7() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var int5 : (int, int) := (0,0);
var int6 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6];
var int7 : (int, int) := (16,17);
var r0 := AddTupleToList(seqint0, int7);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int7;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 8.177985 s

method {:test} Test8() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var int5 : (int, int) := (0,0);
var int6 : (int, int) := (0,0);
var int7 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7];
var int8 : (int, int) := (19,18);
var r0 := AddTupleToList(seqint0, int8);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int8;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 9 - TIME: 8.8676348 s

method {:test} Test9() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var int5 : (int, int) := (0,0);
var int6 : (int, int) := (0,0);
var int7 : (int, int) := (0,0);
var int8 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8];
var int9 : (int, int) := (20,21);
var r0 := AddTupleToList(seqint0, int9);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int9;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 10 - TIME: 9.6373197 s
