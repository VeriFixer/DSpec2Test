method {:testEntry} AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{
    result := [];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
    {
        result := result + [a[i] + b[i]];
    }
}

method {:test} Test8() {
var seqint0 : seq<int> := [-5244];
var seqint1 : seq<int> := [5853];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 9 - TIME: 9.9751836 s
