
method {:test} Test8() {
var seqint0 : seq<int> := [7373, 0, 0, 5850, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2139, 0, 1235, 0, 7886];
var seqint1 : seq<int> := [-1, 0, 0, -5851, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2140, 0, -1, 0, -1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 9 - TIME: 10.7559631 s