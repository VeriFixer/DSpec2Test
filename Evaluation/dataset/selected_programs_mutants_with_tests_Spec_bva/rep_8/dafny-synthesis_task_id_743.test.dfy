
method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 11, 0, 9, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 21, 19];
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 107);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 107 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 12.7550414 s