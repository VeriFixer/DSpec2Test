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

// REPEAT 1 - TIME: 2.822492 s

method {:test} Test1() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20];
var int21 : (int, int) := (4,5);
var r0 := AddTupleToList(seqint0, int21);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int21;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 2 - TIME: 3.6764375 s

method {:test} Test2() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21];
var int22 : (int, int) := (7,6);
var r0 := AddTupleToList(seqint0, int22);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int22;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 3 - TIME: 4.5279332 s

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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22];
var int23 : (int, int) := (8,9);
var r0 := AddTupleToList(seqint0, int23);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int23;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 4 - TIME: 5.4797237 s

method {:test} Test4() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23];
var int24 : (int, int) := (11,10);
var r0 := AddTupleToList(seqint0, int24);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int24;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 5 - TIME: 6.3586322 s

method {:test} Test5() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24];
var int25 : (int, int) := (13,12);
var r0 := AddTupleToList(seqint0, int25);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int25;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 6 - TIME: 7.3154478 s

method {:test} Test6() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25];
var int26 : (int, int) := (14,15);
var r0 := AddTupleToList(seqint0, int26);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int26;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 7 - TIME: 8.0390734 s

method {:test} Test7() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26];
var int27 : (int, int) := (17,16);
var r0 := AddTupleToList(seqint0, int27);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int27;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 8.7329117 s

method {:test} Test8() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27];
var int28 : (int, int) := (19,18);
var r0 := AddTupleToList(seqint0, int28);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int28;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 9 - TIME: 9.4933852 s

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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28];
var int29 : (int, int) := (20,21);
var r0 := AddTupleToList(seqint0, int29);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int29;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 10 - TIME: 10.150764 s
