
method {:test} Test12() {
var seqint0 : seq<int> := [1, 0];
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 101);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 101 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 7.2298074 s