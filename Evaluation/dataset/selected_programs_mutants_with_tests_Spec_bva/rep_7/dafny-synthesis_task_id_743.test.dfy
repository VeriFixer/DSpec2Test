
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 106);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 106 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 12.101945 s