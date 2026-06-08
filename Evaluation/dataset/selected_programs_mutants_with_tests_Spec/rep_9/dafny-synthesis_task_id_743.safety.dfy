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

method {:test} Test8() {
var seqint0 : seq<int> := [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 25, 0, 23];
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 8);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 8 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 11.4835682 s
