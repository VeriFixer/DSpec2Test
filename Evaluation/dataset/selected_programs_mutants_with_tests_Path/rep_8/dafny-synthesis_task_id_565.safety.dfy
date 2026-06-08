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
var r0 := SplitStringIntoChars("\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}");
expect |r0| == |"\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"| ==> r0[i] == "\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"[i];
}

// REPEAT 8 - TIME: 73.07867 s
