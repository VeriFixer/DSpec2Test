
method {:test} Test12() {
var seqint0 : seq<int> := [29, 3, 5, 7, 0];
expect 2284 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2284, 4);
expect r0 == seqint0[(4 - 2284 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 9.4704304 s