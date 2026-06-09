
method {:test} Test9() {
var seqint0 : seq<int> := [306, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [325, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [324, 0, 0, 0, 0];
var seqint3 : seq<int> := [323, 0, 0, 0];
var seqint4 : seq<int> := [322, 0, 0, 0];
var seqint5 : seq<int> := [321, 0, 0, 0];
var seqint6 : seq<int> := [320, 0, 0, 0];
var seqint7 : seq<int> := [319, 0, 0, 0];
var seqint8 : seq<int> := [318, 0, 0, 0];
var seqint9 : seq<int> := [317, 0, 0, 0];
var seqint10 : seq<int> := [316, 0, 0, 0];
var seqint11 : seq<int> := [315, 0, 0, 0];
var seqint12 : seq<int> := [314, 0, 0, 0];
var seqint13 : seq<int> := [313, 0, 0, 0];
var seqint14 : seq<int> := [312, 0, 0, 0];
var seqint15 : seq<int> := [311, 0, 0, 0];
var seqint16 : seq<int> := [310, 0, 0, 0];
var seqint17 : seq<int> := [309, 0, 0, 0, 0];
var seqint18 : seq<int> := [308, 0, 0, 0, 0];
var seqint19 : seq<int> := [307, 0, 0];
var seqint20 : seq<int> := [326, 0];
var seqint21 : seq<int> := [327];
var seqint22 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 103.414632 s