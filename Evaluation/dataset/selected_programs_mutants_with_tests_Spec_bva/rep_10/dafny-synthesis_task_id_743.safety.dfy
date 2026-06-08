method {:testEntry} RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
    var rotated: seq<int> := [];
    for i := 0 to |l|
        invariant 0 <= i <= |l|
        invariant |rotated| == i
        invariant forall k :: 0 <= k < i ==> rotated[k] == l[(k - n + |l|) % |l|]
    {
        rotated := rotated + [l[(i - n + |l|) % |l|]];
    }
    return rotated;
}

method {:test} Test20() {
var seqint0 : seq<int> := [24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 22, 0];
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 109);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 109 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 14.1963592 s
