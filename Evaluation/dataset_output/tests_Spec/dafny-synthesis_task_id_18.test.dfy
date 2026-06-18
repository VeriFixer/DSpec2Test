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

method {:test} Test0() {
var r0 := RemoveChars("a", "");
expect |r0| <= |"a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a" && !(r0[i] in "");
expect forall i :: 0 <= i < |"a"| ==> "a"[i] in "" || "a"[i] in r0;
}

// REPEAT 1 - TIME: 2.8744481 s

method {:test} Test1() {
var r0 := RemoveChars("a\U{0002}", "aaaaaa\U{0002}a\0");
expect |r0| <= |"a\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\U{0002}" && !(r0[i] in "aaaaaa\U{0002}a\0");
expect forall i :: 0 <= i < |"a\U{0002}"| ==> "a\U{0002}"[i] in "aaaaaa\U{0002}a\0" || "a\U{0002}"[i] in r0;
}

// REPEAT 2 - TIME: 3.8468272 s

method {:test} Test2() {
var r0 := RemoveChars("aaa", "\0");
expect |r0| <= |"aaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa" && !(r0[i] in "\0");
expect forall i :: 0 <= i < |"aaa"| ==> "aaa"[i] in "\0" || "aaa"[i] in r0;
}

// REPEAT 3 - TIME: 4.7648547 s

method {:test} Test3() {
var r0 := RemoveChars("\U{0002}\0a", "\0\U{0002}");
expect |r0| <= |"\U{0002}\0a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0a" && !(r0[i] in "\0\U{0002}");
expect forall i :: 0 <= i < |"\U{0002}\0a"| ==> "\U{0002}\0a"[i] in "\0\U{0002}" || "\U{0002}\0a"[i] in r0;
}

// REPEAT 4 - TIME: 5.6360066 s

method {:test} Test4() {
var r0 := RemoveChars("\U{0004}aaa", "\U{0006}\0aaaaaaaa\U{0004}a\U{0002}");
expect |r0| <= |"\U{0004}aaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}aaa" && !(r0[i] in "\U{0006}\0aaaaaaaa\U{0004}a\U{0002}");
expect forall i :: 0 <= i < |"\U{0004}aaa"| ==> "\U{0004}aaa"[i] in "\U{0006}\0aaaaaaaa\U{0004}a\U{0002}" || "\U{0004}aaa"[i] in r0;
}

// REPEAT 5 - TIME: 6.6186522 s

method {:test} Test5() {
var r0 := RemoveChars("\0aa", "\U{0002}a\0");
expect |r0| <= |"\0aa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0aa" && !(r0[i] in "\U{0002}a\0");
expect forall i :: 0 <= i < |"\0aa"| ==> "\0aa"[i] in "\U{0002}a\0" || "\0aa"[i] in r0;
}

// REPEAT 6 - TIME: 7.5722031 s

method {:test} Test6() {
var r0 := RemoveChars("\U{0002}a", "\U{0004}aaaa\0a\U{0002}aaaaa\U{0006}");
expect |r0| <= |"\U{0002}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}a" && !(r0[i] in "\U{0004}aaaa\0a\U{0002}aaaaa\U{0006}");
expect forall i :: 0 <= i < |"\U{0002}a"| ==> "\U{0002}a"[i] in "\U{0004}aaaa\0a\U{0002}aaaaa\U{0006}" || "\U{0002}a"[i] in r0;
}

// REPEAT 7 - TIME: 8.291749 s

method {:test} Test7() {
var r0 := RemoveChars("\U{0008}aa\U{0002}aaaaaa\U{0006}", "\U{0006}\0\U{0008}\U{0004}a\U{0002}aaa\n");
expect |r0| <= |"\U{0008}aa\U{0002}aaaaaa\U{0006}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0008}aa\U{0002}aaaaaa\U{0006}" && !(r0[i] in "\U{0006}\0\U{0008}\U{0004}a\U{0002}aaa\n");
expect forall i :: 0 <= i < |"\U{0008}aa\U{0002}aaaaaa\U{0006}"| ==> "\U{0008}aa\U{0002}aaaaaa\U{0006}"[i] in "\U{0006}\0\U{0008}\U{0004}a\U{0002}aaa\n" || "\U{0008}aa\U{0002}aaaaaa\U{0006}"[i] in r0;
}

// REPEAT 8 - TIME: 9.0328484 s

method {:test} Test8() {
var r0 := RemoveChars("\U{0004}aa\U{0004}\U{0004}", "\U{0002}\0");
expect |r0| <= |"\U{0004}aa\U{0004}\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}aa\U{0004}\U{0004}" && !(r0[i] in "\U{0002}\0");
expect forall i :: 0 <= i < |"\U{0004}aa\U{0004}\U{0004}"| ==> "\U{0004}aa\U{0004}\U{0004}"[i] in "\U{0002}\0" || "\U{0004}aa\U{0004}\U{0004}"[i] in r0;
}

// REPEAT 9 - TIME: 9.7047462 s

method {:test} Test9() {
var r0 := RemoveChars("\naaaaaa\U{0006}a\U{0008}a\U{000E}", "\U{0004}\U{0002}a\U{000E}a\U{0008}a\0a\U{000C}\U{0006}a\n\U{0010}\U{0012}");
expect |r0| <= |"\naaaaaa\U{0006}a\U{0008}a\U{000E}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\naaaaaa\U{0006}a\U{0008}a\U{000E}" && !(r0[i] in "\U{0004}\U{0002}a\U{000E}a\U{0008}a\0a\U{000C}\U{0006}a\n\U{0010}\U{0012}");
expect forall i :: 0 <= i < |"\naaaaaa\U{0006}a\U{0008}a\U{000E}"| ==> "\naaaaaa\U{0006}a\U{0008}a\U{000E}"[i] in "\U{0004}\U{0002}a\U{000E}a\U{0008}a\0a\U{000C}\U{0006}a\n\U{0010}\U{0012}" || "\naaaaaa\U{0006}a\U{0008}a\U{000E}"[i] in r0;
}

// REPEAT 10 - TIME: 10.4660632 s
