
method {:test} Test8() {
var seqint0 : seq<int> := [130, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [136, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [134, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [133, 0, 0, 0];
var seqint4 : seq<int> := [132, 0, 0];
var seqint5 : seq<int> := [131, 0];
var seqint6 : seq<int> := [135, 0];
var seqint7 : seq<int> := [183];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 9.872918 s