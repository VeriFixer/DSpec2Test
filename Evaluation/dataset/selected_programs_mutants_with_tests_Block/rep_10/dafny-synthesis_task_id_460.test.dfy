
method {:test} Test9() {
var seqint0 : seq<int> := [9];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [];
var seqint9 : seq<int> := [];
var seqint10 : seq<int> := [];
var seqint11 : seq<int> := [];
var seqint12 : seq<int> := [];
var seqint13 : seq<int> := [0];
var seqint14 : seq<int> := [];
var seqint15 : seq<int> := [];
var seqint16 : seq<int> := [];
var seqint17 : seq<int> := [];
var seqint18 : seq<int> := [];
var seqint19 : seq<int> := [0];
var seqint20 : seq<int> := [0];
var seqint21 : seq<int> := [];
var seqint22 : seq<int> := [];
var seqint23 : seq<int> := [];
var seqint24 : seq<int> := [];
var seqint25 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 9.4720305 s