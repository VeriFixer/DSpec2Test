
method {:test} Test8() {
var seqint0 : seq<int> := [0, 14, 0, 11, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 39];
expect 8510 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 36 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8510, 36);
expect r0 == seqint0[(36 - 8510 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 16.979847 s