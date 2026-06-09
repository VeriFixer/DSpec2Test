
method {:test} Test5() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [10, 2, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountIdenticalPositions(seqint0, seqint1, seqint2);
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.3548283 s