
method {:test} Test9() {
var seqint0 : seq<int> := [219];
var seqint1 : seq<int> := [211];
var seqint2 : seq<int> := [206];
var seqint3 : seq<int> := [205];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 12.2543912 s