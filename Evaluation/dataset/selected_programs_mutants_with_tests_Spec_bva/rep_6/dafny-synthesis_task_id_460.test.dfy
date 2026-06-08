
method {:test} Test14() {
var seqint0 : seq<int> := [51];
var seqint1 : seq<int> := [47];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [49];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 11.3234168 s