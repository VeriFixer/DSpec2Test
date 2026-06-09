method {:testEntry} RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{
    var v' : string := [];
    for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v'| <= i
    invariant forall k :: 0 <= k < |v'| ==> (v'[k] in s1) && !(v'[k] in s2)
    invariant forall k :: 0 <= k < i ==> (s1[k] in s2) || (s1[k] in v')
    {
        if !(s1[i] in s2)
        {
            v' := v' + [s1[i]];
        }
    }
    return v';
}

method {:test} Test4() {
var r0 := RemoveChars("\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0" && !(r0[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0002}" || "\0"[i] in r0;
}
method {:test} Test5() {
var r0 := RemoveChars("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}" && !(r0[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"| ==> "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}" || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"[i] in r0;
}

// REPEAT 3 - TIME: 4.9481334 s
