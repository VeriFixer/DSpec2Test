
method {:test} Test7() {
var seqint0 : seq<int> := [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38];
expect 2415 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 34 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2415, 34);
expect r0 == seqint0[(34 - 2415 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 9.0808888 s