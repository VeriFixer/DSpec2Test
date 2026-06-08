
method {:test} Test18() {
var seqint0 : seq<int> := [97];
var seqint1 : seq<int> := [83];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [86];
var seqint5 : seq<int> := [95];
var seqint6 : seq<int> := [99];
var seqint7 : seq<int> := [90];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 13.9735583 s