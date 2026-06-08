
method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 1940, 1965, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3609, 0, 0, 0, 0, 0, 0, 9992, 0, 0, 0, 9501];
var seqint1 : seq<int> := [0, 0, -1941, -1966, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -9993, 0, 0, 0, -9502];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 5 - TIME: 11.3209267 s