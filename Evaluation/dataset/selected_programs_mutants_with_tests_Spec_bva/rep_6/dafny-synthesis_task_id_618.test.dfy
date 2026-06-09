
method {:test} Test17() {
var seqint0 : seq<int> := [8404, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3714, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 609, 0, 0, 0, 0, 9725];
var seqint1 : seq<int> := [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5530, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 6 - TIME: 11.2192047 s