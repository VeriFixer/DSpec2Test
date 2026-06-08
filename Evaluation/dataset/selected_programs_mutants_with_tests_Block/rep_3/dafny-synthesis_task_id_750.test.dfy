
method {:test} Test2() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1];
var int2 : (int, int) := (6,7);
var r0 := AddTupleToList(seqint0, int2);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int2;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 3 - TIME: 3.7446395 s