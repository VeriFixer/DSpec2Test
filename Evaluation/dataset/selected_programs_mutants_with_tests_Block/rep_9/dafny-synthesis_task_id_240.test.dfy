
method {:test} Test8() {
var seqint0 : seq<int> := [31, 0, 0, 0, 0, 29, 0, 0];
var seqint1 : seq<int> := [33, 0, 0, 0, 27, 0, 0, 22, 0, 0, 0, 0, 0, 0, 25];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 9 - TIME: 9.340314 s