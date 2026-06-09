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

method {:test} Test2() {
var r0 := SplitStringIntoChars("aaa");
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> r0[i] == "aaa"[i];
}

// REPEAT 3 - TIME: 4.1647725 s
