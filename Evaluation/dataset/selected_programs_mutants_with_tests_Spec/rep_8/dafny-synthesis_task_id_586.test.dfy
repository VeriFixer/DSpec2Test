
method {:test} Test7() {
var seqint0 : seq<int> := [11, 0, 0, 0, 8, 0, 0, 13];
expect 7 >= 0 && 7 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 7);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 7) % |seqint0|];
}

// REPEAT 8 - TIME: 8.73865 s