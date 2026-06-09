method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
    v := [];
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall k :: 0 <= k < i ==> v[k] == s[k]
    {
        v := v + [s[i]];
    }
}

method {:test} Test7() {
var r0 := SplitStringIntoChars("\U{0002}\0aa");
expect |r0| == |"\U{0002}\0aa"|;
expect forall i :: 0 <= i < |"\U{0002}\0aa"| ==> r0[i] == "\U{0002}\0aa"[i];
}

// REPEAT 8 - TIME: 7.928443 s
