
method {:test} Test6() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 8462 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 28 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8462, 28);
expect r0 == seqint0[(28 - 8462 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 8.8383878 s