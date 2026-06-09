
method {:test} Test18() {
var seqint0 : seq<int> := [411, 406, 408];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 10 - TIME: 13.9266885 s