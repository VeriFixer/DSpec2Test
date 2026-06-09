method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{
    element := l[(index - n + |l|) % |l|];
}

method {:test} Test5() {
var seqint0 : seq<int> := [10, 5, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
expect 8420 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 26 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8420, 26);
expect r0 == seqint0[(26 - 8420 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 5.8610699 s
