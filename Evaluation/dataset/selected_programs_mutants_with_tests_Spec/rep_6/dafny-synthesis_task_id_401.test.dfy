
method {:test} Test5() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7];
var seqint8 : seq<int> := [0];
var seqint9 : seq<int> := [];
var seqint10 : seq<int> := [];
var seqint11 : seq<int> := [0];
var seqint12 : seq<int> := [];
var seqint13 : seq<int> := [];
var seqint14 : seq<int> := [];
var seqint15 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 6 - TIME: 8.6049862 s