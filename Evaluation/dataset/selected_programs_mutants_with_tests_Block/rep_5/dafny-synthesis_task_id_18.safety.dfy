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

method {:test} Test8() {
var r0 := RemoveChars("\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\U{000C}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0002}\0a\U{000C}\U{0006}\n\U{0008}");
expect |r0| <= |"\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\U{000C}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\U{000C}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0002}\0a\U{000C}\U{0006}\n\U{0008}");
expect forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\U{000C}"| ==> "\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\U{000C}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0002}\0a\U{000C}\U{0006}\n\U{0008}" || "\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\U{000C}"[i] in r0;
}
method {:test} Test9() {
var r0 := RemoveChars("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}a\U{000E}", "aa\U{0010}aaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\U{0008}\naa\U{000C}");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}a\U{000E}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}a\U{000E}" && !(r0[i] in "aa\U{0010}aaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\U{0008}\naa\U{000C}");
expect forall i :: 0 <= i < |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}a\U{000E}"| ==> "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}a\U{000E}"[i] in "aa\U{0010}aaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\U{0008}\naa\U{000C}" || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}a\U{000E}"[i] in r0;
}

// REPEAT 5 - TIME: 8.0297349 s
