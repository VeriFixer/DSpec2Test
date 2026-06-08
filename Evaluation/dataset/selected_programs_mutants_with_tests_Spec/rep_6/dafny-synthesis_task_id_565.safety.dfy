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

method {:test} Test5() {
var r0 := SplitStringIntoChars("\U{0002}\0a");
expect |r0| == |"\U{0002}\0a"|;
expect forall i :: 0 <= i < |"\U{0002}\0a"| ==> r0[i] == "\U{0002}\0a"[i];
}

// REPEAT 6 - TIME: 7.8361562 s
