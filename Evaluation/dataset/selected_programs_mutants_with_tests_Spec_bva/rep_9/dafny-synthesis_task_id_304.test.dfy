
method {:test} Test18() {
var seqint0 : seq<int> := [35, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 32, 22, 0, 41];
expect 2405 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 36 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2405, 36);
expect r0 == seqint0[(36 - 2405 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 15.0098087 s