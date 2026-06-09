
method {:test} Test8() {
var seqint0 : seq<int> := [213, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [232, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [231, 0, 0, 0];
var seqint3 : seq<int> := [230, 0, 0];
var seqint4 : seq<int> := [229, 0, 0];
var seqint5 : seq<int> := [228, 0, 0];
var seqint6 : seq<int> := [227, 0, 0];
var seqint7 : seq<int> := [226, 0, 0];
var seqint8 : seq<int> := [225, 0, 0];
var seqint9 : seq<int> := [224, 0, 0];
var seqint10 : seq<int> := [223, 0, 0];
var seqint11 : seq<int> := [222, 0, 0];
var seqint12 : seq<int> := [221, 0, 0];
var seqint13 : seq<int> := [220, 0, 0];
var seqint14 : seq<int> := [219, 0, 0];
var seqint15 : seq<int> := [218, 0, 0];
var seqint16 : seq<int> := [217, 0, 0];
var seqint17 : seq<int> := [216, 0, 0, 0];
var seqint18 : seq<int> := [215, 0, 0, 0];
var seqint19 : seq<int> := [214, 0];
var seqint20 : seq<int> := [233];
var seqint21 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 79.2553839 s