
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 5 - TIME: 7.0380646 s