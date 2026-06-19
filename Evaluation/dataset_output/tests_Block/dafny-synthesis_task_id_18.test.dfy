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
var r0 := RemoveChars("", "");
expect |r0| <= |""|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "" && !(r0[i] in "");
expect forall i :: 0 <= i < |""| ==> ""[i] in "" || ""[i] in r0;
}
method {:test} Test1() {
var r0 := RemoveChars("a\0", "");
expect |r0| <= |"a\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0" && !(r0[i] in "");
expect forall i :: 0 <= i < |"a\0"| ==> "a\0"[i] in "" || "a\0"[i] in r0;
}

// REPEAT 1 - TIME: 2.3498074 s

method {:test} Test2() {
var r0 := RemoveChars("\0", "a");
expect |r0| <= |"\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0" && !(r0[i] in "a");
expect forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "a" || "\0"[i] in r0;
}
method {:test} Test3() {
var r0 := RemoveChars("aa\0", "aaaaaaaaa\U{0002}");
expect |r0| <= |"aa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aa\0" && !(r0[i] in "aaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"aa\0"| ==> "aa\0"[i] in "aaaaaaaaa\U{0002}" || "aa\0"[i] in r0;
}

// REPEAT 2 - TIME: 3.5189308 s

method {:test} Test4() {
var r0 := RemoveChars("\0a", "a\0");
expect |r0| <= |"\0a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0a" && !(r0[i] in "a\0");
expect forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] in "a\0" || "\0a"[i] in r0;
}
method {:test} Test5() {
var r0 := RemoveChars("\U{0002}\0", "\U{0002}a");
expect |r0| <= |"\U{0002}\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0" && !(r0[i] in "\U{0002}a");
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "\U{0002}a" || "\U{0002}\0"[i] in r0;
}

// REPEAT 3 - TIME: 4.5899909 s

method {:test} Test6() {
var r0 := RemoveChars("\0", "\0");
expect |r0| <= |"\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0" && !(r0[i] in "\0");
expect forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "\0" || "\0"[i] in r0;
}
method {:test} Test7() {
var r0 := RemoveChars("a\0aa", "aa\U{0002}");
expect |r0| <= |"a\0aa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aa" && !(r0[i] in "aa\U{0002}");
expect forall i :: 0 <= i < |"a\0aa"| ==> "a\0aa"[i] in "aa\U{0002}" || "a\0aa"[i] in r0;
}

// REPEAT 4 - TIME: 5.9802668 s

method {:test} Test8() {
var r0 := RemoveChars("\U{0004}aaa", "\U{0002}a\U{0004}\0");
expect |r0| <= |"\U{0004}aaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}aaa" && !(r0[i] in "\U{0002}a\U{0004}\0");
expect forall i :: 0 <= i < |"\U{0004}aaa"| ==> "\U{0004}aaa"[i] in "\U{0002}a\U{0004}\0" || "\U{0004}aaa"[i] in r0;
}
method {:test} Test9() {
var r0 := RemoveChars("a\0aaa", "aaaa");
expect |r0| <= |"a\0aaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaa" && !(r0[i] in "aaaa");
expect forall i :: 0 <= i < |"a\0aaa"| ==> "a\0aaa"[i] in "aaaa" || "a\0aaa"[i] in r0;
}

// REPEAT 5 - TIME: 7.3205596 s

method {:test} Test10() {
var r0 := RemoveChars("\0aaa\U{0004}a", "\U{0002}aaaaaaaa\0aaaaaaaaaaa\U{0004}aaaaa\U{0006}");
expect |r0| <= |"\0aaa\U{0004}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0aaa\U{0004}a" && !(r0[i] in "\U{0002}aaaaaaaa\0aaaaaaaaaaa\U{0004}aaaaa\U{0006}");
expect forall i :: 0 <= i < |"\0aaa\U{0004}a"| ==> "\0aaa\U{0004}a"[i] in "\U{0002}aaaaaaaa\0aaaaaaaaaaa\U{0004}aaaaa\U{0006}" || "\0aaa\U{0004}a"[i] in r0;
}
method {:test} Test11() {
var r0 := RemoveChars("a\0aaaa", "aaaaa");
expect |r0| <= |"a\0aaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaa" && !(r0[i] in "aaaaa");
expect forall i :: 0 <= i < |"a\0aaaa"| ==> "a\0aaaa"[i] in "aaaaa" || "a\0aaaa"[i] in r0;
}

// REPEAT 6 - TIME: 8.4854632 s

method {:test} Test12() {
var r0 := RemoveChars("\0", "\0");
expect |r0| <= |"\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0" && !(r0[i] in "\0");
expect forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "\0" || "\0"[i] in r0;
}
method {:test} Test13() {
var r0 := RemoveChars("\U{0002}\0aaa", "aa\U{0002}aaa");
expect |r0| <= |"\U{0002}\0aaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0aaa" && !(r0[i] in "aa\U{0002}aaa");
expect forall i :: 0 <= i < |"\U{0002}\0aaa"| ==> "\U{0002}\0aaa"[i] in "aa\U{0002}aaa" || "\U{0002}\0aaa"[i] in r0;
}

// REPEAT 7 - TIME: 9.3701734 s

method {:test} Test14() {
var r0 := RemoveChars("aaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}", "\0\U{0004}aaa\U{0002}aaaaaaaaaaaaaaaaa\U{0006}aaaa\U{0008}");
expect |r0| <= |"aaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}" && !(r0[i] in "\0\U{0004}aaa\U{0002}aaaaaaaaaaaaaaaaa\U{0006}aaaa\U{0008}");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}"| ==> "aaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}"[i] in "\0\U{0004}aaa\U{0002}aaaaaaaaaaaaaaaaa\U{0006}aaaa\U{0008}" || "aaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}"[i] in r0;
}
method {:test} Test15() {
var r0 := RemoveChars("a\0aaa\U{0006}\U{0006}", "\U{0002}\U{0006}\U{0004}");
expect |r0| <= |"a\0aaa\U{0006}\U{0006}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaa\U{0006}\U{0006}" && !(r0[i] in "\U{0002}\U{0006}\U{0004}");
expect forall i :: 0 <= i < |"a\0aaa\U{0006}\U{0006}"| ==> "a\0aaa\U{0006}\U{0006}"[i] in "\U{0002}\U{0006}\U{0004}" || "a\0aaa\U{0006}\U{0006}"[i] in r0;
}

// REPEAT 8 - TIME: 10.1671022 s

method {:test} Test16() {
var r0 := RemoveChars("aaaaaaa\U{0006}aaa\U{0002}aaaaaaaaaa\U{0002}", "\0aaaa\U{0006}a\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaa\U{0008}a");
expect |r0| <= |"aaaaaaa\U{0006}aaa\U{0002}aaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaa\U{0006}aaa\U{0002}aaaaaaaaaa\U{0002}" && !(r0[i] in "\0aaaa\U{0006}a\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaa\U{0008}a");
expect forall i :: 0 <= i < |"aaaaaaa\U{0006}aaa\U{0002}aaaaaaaaaa\U{0002}"| ==> "aaaaaaa\U{0006}aaa\U{0002}aaaaaaaaaa\U{0002}"[i] in "\0aaaa\U{0006}a\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaa\U{0008}a" || "aaaaaaa\U{0006}aaa\U{0002}aaaaaaaaaa\U{0002}"[i] in r0;
}
method {:test} Test17() {
var r0 := RemoveChars("a\0aaaaa\U{0008}a\U{000C}aaaaaaaaaaaaa", "\U{0002}a\U{0008}a\U{0004}aaaaaaaaaaaaaa\U{0006}\U{000C}\U{000E}aaaa\na\U{0010}a");
expect |r0| <= |"a\0aaaaa\U{0008}a\U{000C}aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaa\U{0008}a\U{000C}aaaaaaaaaaaaa" && !(r0[i] in "\U{0002}a\U{0008}a\U{0004}aaaaaaaaaaaaaa\U{0006}\U{000C}\U{000E}aaaa\na\U{0010}a");
expect forall i :: 0 <= i < |"a\0aaaaa\U{0008}a\U{000C}aaaaaaaaaaaaa"| ==> "a\0aaaaa\U{0008}a\U{000C}aaaaaaaaaaaaa"[i] in "\U{0002}a\U{0008}a\U{0004}aaaaaaaaaaaaaa\U{0006}\U{000C}\U{000E}aaaa\na\U{0010}a" || "a\0aaaaa\U{0008}a\U{000C}aaaaaaaaaaaaa"[i] in r0;
}

// REPEAT 9 - TIME: 11.147423 s

method {:test} Test18() {
var r0 := RemoveChars("\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaa", "\0aaaaaa\U{0006}aaaaaa\U{0002}aaaaaaaa\U{0004}aaaa");
expect |r0| <= |"\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaa" && !(r0[i] in "\0aaaaaa\U{0006}aaaaaa\U{0002}aaaaaaaa\U{0004}aaaa");
expect forall i :: 0 <= i < |"\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaa"| ==> "\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaa"[i] in "\0aaaaaa\U{0006}aaaaaa\U{0002}aaaaaaaa\U{0004}aaaa" || "\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaa"[i] in r0;
}
method {:test} Test19() {
var r0 := RemoveChars("\U{0006}\0aaaaa\U{0004}", "\U{0002}aaaa\U{0004}aaaa\U{0006}aaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0006}\0aaaaa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0006}\0aaaaa\U{0004}" && !(r0[i] in "\U{0002}aaaa\U{0004}aaaa\U{0006}aaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"\U{0006}\0aaaaa\U{0004}"| ==> "\U{0006}\0aaaaa\U{0004}"[i] in "\U{0002}aaaa\U{0004}aaaa\U{0006}aaaaaaaaaaaaaaaaaa" || "\U{0006}\0aaaaa\U{0004}"[i] in r0;
}

// REPEAT 10 - TIME: 12.1404031 s
