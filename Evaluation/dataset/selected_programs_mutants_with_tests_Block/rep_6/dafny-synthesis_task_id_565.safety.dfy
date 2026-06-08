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
var r0 := SplitStringIntoChars("\0aa\U{0002}");
expect |r0| == |"\0aa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}"| ==> r0[i] == "\0aa\U{0002}"[i];
}

// REPEAT 6 - TIME: 6.1325514 s
