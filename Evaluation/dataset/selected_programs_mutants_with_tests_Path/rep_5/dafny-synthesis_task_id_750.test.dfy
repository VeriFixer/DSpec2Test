
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

// REPEAT 5 - TIME: 7.2870372 s