
method {:test} Test16() {
var seqint0 : seq<int> := [70];
var seqint1 : seq<int> := [68];
var seqint2 : seq<int> := [66];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [69];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 12.6377444 s