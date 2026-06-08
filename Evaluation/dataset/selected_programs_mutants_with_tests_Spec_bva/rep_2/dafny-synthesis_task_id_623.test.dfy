
method {:test} Test12() {
var seqint0 : seq<int> := [1, 0];
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 101);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 101);
}

// REPEAT 2 - TIME: 9.7342091 s