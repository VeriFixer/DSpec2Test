
method {:test} Test8() {
var seqint0 : seq<int> := [14, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 2479 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 35 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2479, 35);
expect r0 == seqint0[(35 - 2479 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 9.4825841 s