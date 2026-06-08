method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{
    element := l[(index - n + |l|) % |l|];
}

method {:test} Test19() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 2464 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 37 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2464, 37);
expect r0 == seqint0[(37 - 2464 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 17.4350359 s
