
method {:test} Test14() {
var seqint0 : seq<int> := [3, 0, 5];
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 103);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 103 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 9.7481769 s