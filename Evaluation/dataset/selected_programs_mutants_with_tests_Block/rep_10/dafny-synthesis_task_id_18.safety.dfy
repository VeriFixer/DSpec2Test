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

method {:test} Test18() {
var r0 := RemoveChars("aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "\U{0004}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "\U{0004}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0002}" || "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}
method {:test} Test19() {
var r0 := RemoveChars("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}

// REPEAT 10 - TIME: 16.4298553 s
