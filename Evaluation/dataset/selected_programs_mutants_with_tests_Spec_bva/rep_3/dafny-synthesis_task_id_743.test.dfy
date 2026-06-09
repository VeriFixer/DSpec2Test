
method {:test} Test13() {
var seqint0 : seq<int> := [2, 0];
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 102);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 102 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 7.7839598 s