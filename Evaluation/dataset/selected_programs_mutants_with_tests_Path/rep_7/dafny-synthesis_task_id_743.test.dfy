
method {:test} Test6() {
var seqint0 : seq<int> := [];
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 6);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 6 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 87.16881 s