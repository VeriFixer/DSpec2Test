
method {:test} Test19() {
var seqint0 : seq<int> := [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14];
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 108);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 108 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 13.481022 s