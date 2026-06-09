
method {:test} Test14() {
var seqint0 : seq<int> := [18, 0, 0, 0, 11, 0, 15];
expect 6 >= 0 && 6 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 6);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 6) % |seqint0|];
}

// REPEAT 7 - TIME: 11.5036002 s