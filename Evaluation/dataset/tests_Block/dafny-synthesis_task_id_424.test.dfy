method {:testEntry} ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{
    var rearChars: seq<char> := [];
    for i := 0 to |l|
        invariant 0 <= i <= |l|
        invariant |rearChars| == i
        invariant forall k :: 0 <= k < i ==> rearChars[k] == l[k][|l[k]| - 1]
    {
        rearChars := rearChars + [l[i][|l[i]| - 1]];
    }
    return rearChars;
}

method {:test} Test0() {
var seqstring0 : seq<string> := [""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 1 - TIME: 2.7667486 s

method {:test} Test1() {
var seqstring0 : seq<string> := ["", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 2 - TIME: 3.8253452 s

method {:test} Test2() {
var seqstring0 : seq<string> := ["", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 3 - TIME: 4.8199201 s

method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 4 - TIME: 5.8222967 s

method {:test} Test4() {
var seqstring0 : seq<string> := ["", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 5 - TIME: 6.8541112 s

method {:test} Test5() {
var seqstring0 : seq<string> := ["", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 6 - TIME: 7.8328955 s

method {:test} Test6() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 7 - TIME: 8.6461067 s

method {:test} Test7() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 8 - TIME: 9.3853832 s

method {:test} Test8() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 9 - TIME: 10.1407768 s

method {:test} Test9() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 10 - TIME: 10.973285 s
