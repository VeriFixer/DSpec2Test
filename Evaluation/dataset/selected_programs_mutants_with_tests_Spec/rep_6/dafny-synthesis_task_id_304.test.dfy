
method {:test} Test5() {
var seqint0 : seq<int> := [6, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
expect 2350 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 27 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2350, 27);
expect r0 == seqint0[(27 - 2350 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 6.542866 s