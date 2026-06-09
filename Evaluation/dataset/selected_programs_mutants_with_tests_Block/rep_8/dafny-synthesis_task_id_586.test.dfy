
method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 22, 0, 0, 26, 0, 0];
expect 49 >= 0 && 49 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 49);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 49) % |seqint0|];
}

// REPEAT 8 - TIME: 8.3465421 s