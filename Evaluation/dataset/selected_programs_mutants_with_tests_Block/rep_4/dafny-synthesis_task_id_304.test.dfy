
method {:test} Test3() {
var seqint0 : seq<int> := [3, 29, 0, 0];
expect 8370 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8370, 3);
expect r0 == seqint0[(3 - 8370 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 4.259285 s