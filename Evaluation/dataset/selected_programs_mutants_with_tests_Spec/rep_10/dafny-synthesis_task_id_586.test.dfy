
method {:test} Test9() {
var seqint0 : seq<int> := [20, 0, 0, 12, 0, 0, 0, 0, 0, 17];
expect 9 >= 0 && 9 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 9);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 9) % |seqint0|];
}

// REPEAT 10 - TIME: 10.2398385 s