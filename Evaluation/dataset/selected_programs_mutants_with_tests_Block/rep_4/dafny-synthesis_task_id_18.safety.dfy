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

method {:test} Test6() {
var r0 := RemoveChars("\0aa\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0004}aaa\U{0006}aa\U{0008}aa\U{0002}");
expect |r0| <= |"\0aa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0aa\U{0002}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0004}aaa\U{0006}aa\U{0008}aa\U{0002}");
expect forall i :: 0 <= i < |"\0aa\U{0002}"| ==> "\0aa\U{0002}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0004}aaa\U{0006}aa\U{0008}aa\U{0002}" || "\0aa\U{0002}"[i] in r0;
}
method {:test} Test7() {
var r0 := RemoveChars("aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}" && !(r0[i] in "a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in r0;
}

// REPEAT 4 - TIME: 6.5991972 s
