
method {:test} Test5() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 6 - TIME: 6.499706 s