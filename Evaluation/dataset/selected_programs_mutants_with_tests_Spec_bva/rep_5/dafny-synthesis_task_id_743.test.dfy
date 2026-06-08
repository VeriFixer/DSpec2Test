
method {:test} Test15() {
var seqint0 : seq<int> := [4, 7];
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 104);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 104 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 10.5240944 s