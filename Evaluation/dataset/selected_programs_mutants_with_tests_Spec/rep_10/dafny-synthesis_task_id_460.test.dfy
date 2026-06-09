
method {:test} Test9() {
var seqint0 : seq<int> := [174, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [173, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [171, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [170, 0, 0, 0, 0];
var seqint4 : seq<int> := [169, 0, 0, 0];
var seqint5 : seq<int> := [177, 0, 0];
var seqint6 : seq<int> := [176, 0, 0];
var seqint7 : seq<int> := [175, 0];
var seqint8 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 10.7662632 s