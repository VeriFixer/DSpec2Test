
method {:test} Test3() {
var seqint0 : seq<int> := [];
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 3);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 3);
}

// REPEAT 4 - TIME: 50.0525781 s