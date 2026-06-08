method {:testEntry} DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
    ensures |copy| == |s|
    ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
{
    var newSeq: seq<int> := [];
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant |newSeq| == i
        invariant forall k :: 0 <= k < i ==> newSeq[k] == s[k]
    {
        newSeq := newSeq + [s[i]];
    }
    return newSeq;
}

method {:test} Test12() {
var seqint0 : seq<int> := [123, 122, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124];
var r0 := DeepCopySeq(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 4 - TIME: 9.7163616 s
