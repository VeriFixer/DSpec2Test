
method {:test} Test6() {
var seqint0 : seq<int> := [17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 11, 13, 15];
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 6);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 6 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 9.3214031 s