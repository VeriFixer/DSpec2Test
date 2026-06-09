
method {:test} Test4() {
expect forall i :: 0 <= i < |""| ==> |""[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ExtractRearChars("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[i][|""[i]| - 1];
}

// REPEAT 5 - TIME: 5.8449732 s