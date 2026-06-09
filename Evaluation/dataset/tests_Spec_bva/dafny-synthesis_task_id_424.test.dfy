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
method {:test} Test1() {
expect forall i :: 0 <= i < |""| ==> |""[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[i][|""[i]| - 1];
}
method {:test} Test3() {
var seqstring0 : seq<string> := ["", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 1 - TIME: 6.3844127 s

method {:test} Test10() {
var seqstring0 : seq<string> := ["", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 2 - TIME: 7.2047635 s

method {:test} Test11() {
var seqstring0 : seq<string> := ["", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 3 - TIME: 7.9182928 s

method {:test} Test12() {
var seqstring0 : seq<string> := ["", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 4 - TIME: 8.5918096 s

method {:test} Test13() {
var seqstring0 : seq<string> := ["", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 5 - TIME: 9.315201 s

method {:test} Test14() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 6 - TIME: 9.9774739 s

method {:test} Test15() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 7 - TIME: 10.5980278 s

method {:test} Test16() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 8 - TIME: 11.0888412 s

method {:test} Test17() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 9 - TIME: 11.6203123 s

method {:test} Test18() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", ""];
expect forall i :: 0 <= i < |seqstring0| ==> |seqstring0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars(seqstring0);
expect |r0| == |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[i] == seqstring0[i][|seqstring0[i]| - 1];
}

// REPEAT 10 - TIME: 12.1522802 s
