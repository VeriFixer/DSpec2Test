
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
var int47 : (int, int) := (17,16);
var r0 := AddTupleToList(seqint0, int47);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int47;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 9.1843825 s