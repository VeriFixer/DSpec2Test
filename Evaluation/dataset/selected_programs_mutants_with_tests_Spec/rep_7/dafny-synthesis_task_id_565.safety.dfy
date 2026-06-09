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

method {:test} Test6() {
var r0 := SplitStringIntoChars("\0aaa");
expect |r0| == |"\0aaa"|;
expect forall i :: 0 <= i < |"\0aaa"| ==> r0[i] == "\0aaa"[i];
}

// REPEAT 7 - TIME: 7.2923121 s
