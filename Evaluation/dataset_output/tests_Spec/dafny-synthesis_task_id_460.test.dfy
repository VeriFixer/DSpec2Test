method {:testEntry} GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
{
    result := [];
    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == lst[j][0]
    {
        result := result + [lst[i][0]];
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 1 - TIME: 2.9183365 s

method {:test} Test1() {
var seqint0 : seq<int> := [25];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 2 - TIME: 3.9345545 s

method {:test} Test2() {
var seqint0 : seq<int> := [30, 0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 3 - TIME: 4.8716076 s

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

// REPEAT 4 - TIME: 5.8395208 s

method {:test} Test4() {
var seqint0 : seq<int> := [47, 0, 0, 0];
var seqint1 : seq<int> := [49, 0];
var seqint2 : seq<int> := [50, 0];
var seqint3 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 5 - TIME: 6.7566311 s

method {:test} Test5() {
var seqint0 : seq<int> := [32, 0, 0, 0, 0];
var seqint1 : seq<int> := [33, 0, 0];
var seqint2 : seq<int> := [31, 0, 0];
var seqint3 : seq<int> := [29];
var seqint4 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 7.6808428 s

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

// REPEAT 7 - TIME: 8.5425938 s

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

// REPEAT 8 - TIME: 9.4436803 s

method {:test} Test8() {
var seqint0 : seq<int> := [130, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [136, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [134, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [133, 0, 0, 0];
var seqint4 : seq<int> := [132, 0, 0];
var seqint5 : seq<int> := [131, 0];
var seqint6 : seq<int> := [135, 0];
var seqint7 : seq<int> := [183];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 10.283345 s

method {:test} Test9() {
var seqint0 : seq<int> := [174, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [173, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [171, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [170, 0, 0, 0, 0];
var seqint4 : seq<int> := [169, 0, 0, 0];
var seqint5 : seq<int> := [177, 0, 0];
var seqint6 : seq<int> := [176, 0, 0];
var seqint7 : seq<int> := [175, 0];
var seqint8 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 11.1274427 s
