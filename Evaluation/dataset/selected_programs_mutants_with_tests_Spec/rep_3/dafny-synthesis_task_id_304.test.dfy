
method {:test} Test2() {
var seqint0 : seq<int> := [28, 0, 0];
expect 2288 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2288, 2);
expect r0 == seqint0[(2 - 2288 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 4.488401 s