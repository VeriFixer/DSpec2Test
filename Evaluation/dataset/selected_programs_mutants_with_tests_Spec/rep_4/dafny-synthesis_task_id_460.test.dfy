
method {:test} Test3() {
var seqint0 : seq<int> := [28, 0, 0];
var seqint1 : seq<int> := [27];
var seqint2 : seq<int> := [39];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 4 - TIME: 5.1297392 s