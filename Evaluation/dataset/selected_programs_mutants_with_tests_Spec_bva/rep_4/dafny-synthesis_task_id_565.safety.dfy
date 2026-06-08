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

method {:test} Test12() {
var r0 := SplitStringIntoChars("a\0aaaaaaaaaaaa\U{0002}");
expect |r0| == |"a\0aaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaa\U{0002}"| ==> r0[i] == "a\0aaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 4 - TIME: 9.0475269 s
