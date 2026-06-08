method {:testEntry} PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
    result := [];
    for i := 0 to |l|
        invariant 0 <= i <= |l|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == Power(l[k], n)
    {
        result := result + [Power(l[i], n)];
    }
}

function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}

method {:test} Test6() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 1];
expect 1579 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1579);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1579);
}

// REPEAT 7 - TIME: 91.68511 s
