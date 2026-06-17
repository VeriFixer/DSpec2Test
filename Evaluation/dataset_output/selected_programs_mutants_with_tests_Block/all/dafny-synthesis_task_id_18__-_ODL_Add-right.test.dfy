// dafny-synthesis_task_id_18.dfy

method {:testEntry} RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && !(v[i] in s2)
  ensures forall i :: 0 <= i < |s1| ==> s1[i] in s2 || s1[i] in v
{
  var v': string := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v'| <= i
    invariant forall k :: 0 <= k < |v'| ==> v'[k] in s1 && !(v'[k] in s2)
    invariant forall k :: 0 <= k < i ==> s1[k] in s2 || s1[k] in v'
  {
    if !(s1[i] in s2) {
      v' := v';
    }
  }
  return v';
}


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
method {:test} Test1() {
var r0 := RemoveChars("a\0", "");
expect |r0| <= |"a\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0" && !(r0[i] in "");
expect forall i :: 0 <= i < |"a\0"| ==> "a\0"[i] in "" || "a\0"[i] in r0;
}

// REPEAT 1 - TIME: 2.5513376 s

method {:test} Test2() {
var r0 := RemoveChars("\U{0002}a\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| <= |"\U{0002}a\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}a\U{0002}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect forall i :: 0 <= i < |"\U{0002}a\U{0002}"| ==> "\U{0002}a\U{0002}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" || "\U{0002}a\U{0002}"[i] in r0;
}
method {:test} Test3() {
var r0 := RemoveChars("\U{0004}\0", "aaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\0" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"\U{0004}\0"| ==> "\U{0004}\0"[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0002}" || "\U{0004}\0"[i] in r0;
}

// REPEAT 2 - TIME: 3.6612185 s

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

// REPEAT 3 - TIME: 4.9165694 s

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

// REPEAT 4 - TIME: 6.5707478 s

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

// REPEAT 5 - TIME: 8.263081 s

method {:test} Test10() {
var r0 := RemoveChars("aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n", "aaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaaaaaaaaa\0\U{0002}aa\naaaaa\U{0004}\U{0006}\U{0008}");
expect |r0| <= |"aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaaaaaaaaa\0\U{0002}aa\naaaaa\U{0004}\U{0006}\U{0008}");
expect forall i :: 0 <= i < |"aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| ==> "aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaaaaaaaaa\0\U{0002}aa\naaaaa\U{0004}\U{0006}\U{0008}" || "aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[i] in r0;
}
method {:test} Test11() {
var r0 := RemoveChars("\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa", "\U{0002}");
expect |r0| <= |"\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa" && !(r0[i] in "\U{0002}");
expect forall i :: 0 <= i < |"\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"| ==> "\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"[i] in "\U{0002}" || "\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"[i] in r0;
}

// REPEAT 6 - TIME: 9.8468438 s

method {:test} Test12() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}
method {:test} Test13() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 7 - TIME: 11.0346229 s

method {:test} Test14() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}
method {:test} Test15() {
var r0 := RemoveChars("a\0a\U{0002}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}aaaaaaaaaaa");
expect |r0| <= |"a\0a\U{0002}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0a\U{0002}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}aaaaaaaaaaa");
expect forall i :: 0 <= i < |"a\0a\U{0002}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "a\0a\U{0002}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}aaaaaaaaaaa" || "a\0a\U{0002}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}

// REPEAT 8 - TIME: 12.3085001 s

method {:test} Test16() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}
method {:test} Test17() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 9 - TIME: 13.5953696 s

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

// REPEAT 10 - TIME: 15.2108257 s
