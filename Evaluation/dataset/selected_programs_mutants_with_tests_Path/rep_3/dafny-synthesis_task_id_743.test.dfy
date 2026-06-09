
method {:test} Test2() {
var seqint0 : seq<int> := [1];
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 2);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 2 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 35.4324764 s