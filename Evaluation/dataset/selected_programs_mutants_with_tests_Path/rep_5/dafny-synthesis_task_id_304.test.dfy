
method {:test} Test4() {
var seqint0 : seq<int> := [4, 0, 0, 27, 6];
expect 8371 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8371, 4);
expect r0 == seqint0[(4 - 8371 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 6.9239015 s