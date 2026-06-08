
method {:test} Test16() {
var seqint0 : seq<int> := [6, 0];
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 105);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 105 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 11.2849556 s