
method {:test} Test6() {
var seqint0 : seq<int> := [52, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [51, 0, 0, 0];
var seqint2 : seq<int> := [50, 0];
var seqint3 : seq<int> := [49];
var seqint4 : seq<int> := [48];
var seqint5 : seq<int> := [47];
var seqint6 : seq<int> := [46];
var seqint7 : seq<int> := [44];
var seqint8 : seq<int> := [42];
var seqint9 : seq<int> := [41];
var seqint10 : seq<int> := [40];
var seqint11 : seq<int> := [39];
var seqint12 : seq<int> := [38];
var seqint13 : seq<int> := [37];
var seqint14 : seq<int> := [36];
var seqint15 : seq<int> := [35];
var seqint16 : seq<int> := [34];
var seqint17 : seq<int> := [53, 0];
var seqint18 : seq<int> := [33, 0];
var seqint19 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 50.17697 s