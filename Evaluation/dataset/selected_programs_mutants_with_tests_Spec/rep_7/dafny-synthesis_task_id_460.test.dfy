
method {:test} Test6() {
var seqint0 : seq<int> := [40, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [37, 0, 0, 0];
var seqint2 : seq<int> := [36, 0, 0, 0];
var seqint3 : seq<int> := [35, 0];
var seqint4 : seq<int> := [34];
var seqint5 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 7.9395259 s