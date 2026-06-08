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

method {:test} Test1() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 2 - TIME: 19.8425474 s
