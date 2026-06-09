method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{
    element := l[(index - n + |l|) % |l|];
}

method {:test} Test4() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0];
expect 2315 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 25 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2315, 25);
expect r0 == seqint0[(25 - 2315 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 5.8172768 s
