
method {:test} Test9() {
var seqint0 : seq<int> := [53, 50, 51];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 10 - TIME: 9.1250995 s