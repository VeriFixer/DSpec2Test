
method {:test} Test1() {
var seqint0 : seq<int> := [0, 28];
expect 8366 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8366, 1);
expect r0 == seqint0[(1 - 8366 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 2.7571724 s