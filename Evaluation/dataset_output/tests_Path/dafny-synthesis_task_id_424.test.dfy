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

// REPEAT 1 - TIME: 8.3197239 s

method {:test} Test1() {
var seqstring0 : seq<string> := ["", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 2 - TIME: 14.7567297 s

method {:test} Test2() {
var seqstring0 : seq<string> := ["", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 3 - TIME: 21.3239293 s

method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 4 - TIME: 29.106531 s

method {:test} Test4() {
var seqstring0 : seq<string> := ["", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 5 - TIME: 35.4476965 s

method {:test} Test5() {
var seqstring0 : seq<string> := ["", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 6 - TIME: 42.2994073 s

method {:test} Test6() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 7 - TIME: 48.717969 s

method {:test} Test7() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 8 - TIME: 54.8813202 s

method {:test} Test8() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 9 - TIME: 62.4453039 s

method {:test} Test9() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 10 - TIME: 69.464032 s
