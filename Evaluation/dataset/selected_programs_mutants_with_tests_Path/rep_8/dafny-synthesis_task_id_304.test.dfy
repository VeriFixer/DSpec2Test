
method {:test} Test7() {
var seqint0 : seq<int> := [9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 8508 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 29 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8508, 29);
expect r0 == seqint0[(29 - 8508 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 9.9506042 s