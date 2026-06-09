
method {:test} Test2() {
var seqint0 : seq<int> := [28];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 3 - TIME: 4.9549603 s