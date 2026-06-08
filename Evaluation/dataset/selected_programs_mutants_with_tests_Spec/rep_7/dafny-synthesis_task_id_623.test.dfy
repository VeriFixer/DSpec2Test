
method {:test} Test6() {
var seqint0 : seq<int> := [2446, 0, 0];
expect 7071 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7071);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7071);
}

// REPEAT 7 - TIME: 9.6043411 s