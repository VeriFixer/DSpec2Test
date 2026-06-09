
method {:test} Test7() {
var seqint0 : seq<int> := [101, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [99, 0, 0, 0, 0];
var seqint2 : seq<int> := [98, 0, 0, 0, 0];
var seqint3 : seq<int> := [103, 0, 0];
var seqint4 : seq<int> := [102, 0];
var seqint5 : seq<int> := [104];
var seqint6 : seq<int> := [116];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 8.8849546 s