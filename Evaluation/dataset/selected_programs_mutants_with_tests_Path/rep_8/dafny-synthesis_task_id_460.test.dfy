
method {:test} Test7() {
var seqint0 : seq<int> := [72, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [71, 0, 0, 0, 0];
var seqint2 : seq<int> := [70, 0, 0];
var seqint3 : seq<int> := [69, 0];
var seqint4 : seq<int> := [68, 0];
var seqint5 : seq<int> := [67, 0];
var seqint6 : seq<int> := [66, 0];
var seqint7 : seq<int> := [65, 0];
var seqint8 : seq<int> := [62, 0];
var seqint9 : seq<int> := [61, 0];
var seqint10 : seq<int> := [60, 0];
var seqint11 : seq<int> := [59, 0];
var seqint12 : seq<int> := [58, 0];
var seqint13 : seq<int> := [57, 0];
var seqint14 : seq<int> := [56, 0];
var seqint15 : seq<int> := [55, 0];
var seqint16 : seq<int> := [54, 0];
var seqint17 : seq<int> := [74, 0, 0];
var seqint18 : seq<int> := [73, 0, 0];
var seqint19 : seq<int> := [75];
var seqint20 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 60.8440372 s