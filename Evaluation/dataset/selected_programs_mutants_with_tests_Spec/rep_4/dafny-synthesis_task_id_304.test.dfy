
method {:test} Test3() {
var seqint0 : seq<int> := [5, 3, 29, 0];
expect 2289 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2289, 3);
expect r0 == seqint0[(3 - 2289 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 5.3220438 s