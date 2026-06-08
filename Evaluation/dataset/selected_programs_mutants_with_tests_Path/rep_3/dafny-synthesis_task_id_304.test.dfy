
method {:test} Test2() {
var seqint0 : seq<int> := [26, 2, 0];
expect 8369 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8369, 2);
expect r0 == seqint0[(2 - 8369 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 5.1497919 s