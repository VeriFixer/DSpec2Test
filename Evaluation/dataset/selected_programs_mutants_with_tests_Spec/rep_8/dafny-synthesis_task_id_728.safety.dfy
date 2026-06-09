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

method {:test} Test7() {
var seqint0 : seq<int> := [9531, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 6906, 0, 0, 0, 0, 1653, 0, 4679, 535, 1323, 0, 590, 0, 9725];
var seqint1 : seq<int> := [-8664, 0, 0, 0, 0, 0, 0, -5244, 0, 0, 1680, 0, 0, 0, 0, 235, 0, -1682, -254, 7133, 0, 1856, 0, -7485];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 8 - TIME: 8.8842561 s
