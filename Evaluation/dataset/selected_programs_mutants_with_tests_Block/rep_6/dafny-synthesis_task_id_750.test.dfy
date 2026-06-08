
method {:test} Test5() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4];
var int5 : (int, int) := (12,13);
var r0 := AddTupleToList(seqint0, int5);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int5;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 6 - TIME: 5.9374897 s