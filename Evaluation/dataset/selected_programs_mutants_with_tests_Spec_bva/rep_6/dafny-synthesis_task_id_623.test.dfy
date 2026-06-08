
method {:test} Test16() {
var seqint0 : seq<int> := [8586, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 1142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4679, 0];
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 105);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 105);
}

// REPEAT 6 - TIME: 13.1694846 s