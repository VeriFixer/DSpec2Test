
method {:test} Test6() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var int5 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5];
var int6 : (int, int) := (14,15);
var r0 := AddTupleToList(seqint0, int6);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int6;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 7 - TIME: 6.6559996 s