
method {:test} Test3() {
var seqint0 : seq<int> := [2, 0, 4];
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 3);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 3 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 48.1561807 s