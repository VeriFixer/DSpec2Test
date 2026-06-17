// dafny-synthesis_task_id_750.dfy

method {:testEntry} AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
  ensures |r| == |l| + 1
  ensures r[|r| - 1] == t
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
  r := l;
}


method {:testEntry} AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
    r := l + [t];
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
var int41 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41];
var int42 : (int, int) := (4,5);
var r0 := AddTupleToList(seqint0, int42);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int42;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 2 - TIME: 7.3246104 s

method {:test} Test10() {
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
var int41 : (int, int) := (0,0);
var int42 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41, int42];
var int43 : (int, int) := (7,6);
var r0 := AddTupleToList(seqint0, int43);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int43;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 3 - TIME: 8.0460918 s

method {:test} Test11() {
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
var int41 : (int, int) := (0,0);
var int42 : (int, int) := (0,0);
var int43 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41, int42, int43];
var int44 : (int, int) := (8,9);
var r0 := AddTupleToList(seqint0, int44);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int44;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 4 - TIME: 8.7951492 s

method {:test} Test12() {
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
var int41 : (int, int) := (0,0);
var int42 : (int, int) := (0,0);
var int43 : (int, int) := (0,0);
var int44 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41, int42, int43, int44];
var int45 : (int, int) := (11,10);
var r0 := AddTupleToList(seqint0, int45);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int45;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 5 - TIME: 9.4803713 s

method {:test} Test13() {
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
var int41 : (int, int) := (0,0);
var int42 : (int, int) := (0,0);
var int43 : (int, int) := (0,0);
var int44 : (int, int) := (0,0);
var int45 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41, int42, int43, int44, int45];
var int46 : (int, int) := (12,13);
var r0 := AddTupleToList(seqint0, int46);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int46;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 6 - TIME: 10.1509777 s

method {:test} Test14() {
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
var int41 : (int, int) := (0,0);
var int42 : (int, int) := (0,0);
var int43 : (int, int) := (0,0);
var int44 : (int, int) := (0,0);
var int45 : (int, int) := (0,0);
var int46 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41, int42, int43, int44, int45, int46];
var int47 : (int, int) := (15,14);
var r0 := AddTupleToList(seqint0, int47);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int47;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 7 - TIME: 10.8194572 s

method {:test} Test15() {
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
var int41 : (int, int) := (0,0);
var int42 : (int, int) := (0,0);
var int43 : (int, int) := (0,0);
var int44 : (int, int) := (0,0);
var int45 : (int, int) := (0,0);
var int46 : (int, int) := (0,0);
var int47 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41, int42, int43, int44, int45, int46, int47];
var int48 : (int, int) := (17,16);
var r0 := AddTupleToList(seqint0, int48);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int48;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 11.3552228 s

method {:test} Test16() {
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
var int41 : (int, int) := (0,0);
var int42 : (int, int) := (0,0);
var int43 : (int, int) := (0,0);
var int44 : (int, int) := (0,0);
var int45 : (int, int) := (0,0);
var int46 : (int, int) := (0,0);
var int47 : (int, int) := (0,0);
var int48 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37, int38, int39, int40, int41, int42, int43, int44, int45, int46, int47, int48];
var int49 : (int, int) := (18,19);
var r0 := AddTupleToList(seqint0, int49);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int49;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 9 - TIME: 11.9836285 s

method {:test} Test17() {
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
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6, int7, int8, int9, int10, int11, int12, int13, int14, int15, int16, int17, int18, int19, int20, int21, int22, int23, int24, int25, int26, int27, int28, int29, int30, int31, int32, int33, int34, int35, int36, int37];
var int38 : (int, int) := (20,21);
var r0 := AddTupleToList(seqint0, int38);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int38;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 10 - TIME: 12.7659161 s
