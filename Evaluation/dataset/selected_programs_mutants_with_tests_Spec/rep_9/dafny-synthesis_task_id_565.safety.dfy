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

method {:test} Test8() {
var r0 := SplitStringIntoChars("\0aaaa");
expect |r0| == |"\0aaaa"|;
expect forall i :: 0 <= i < |"\0aaaa"| ==> r0[i] == "\0aaaa"[i];
}

// REPEAT 9 - TIME: 10.2150725 s
