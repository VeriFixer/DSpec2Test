
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

// REPEAT 4 - TIME: 4.4273652 s