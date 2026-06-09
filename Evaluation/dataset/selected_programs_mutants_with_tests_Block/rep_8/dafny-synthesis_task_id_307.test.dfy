
method {:test} Test7() {
var seqint0 : seq<int> := [39, 0, 40];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 9.3709469 s