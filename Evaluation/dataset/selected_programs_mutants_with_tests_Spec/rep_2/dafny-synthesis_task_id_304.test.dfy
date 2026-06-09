
method {:test} Test1() {
var seqint0 : seq<int> := [27, 1];
expect 2283 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2283, 1);
expect r0 == seqint0[(1 - 2283 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 3.2892203 s