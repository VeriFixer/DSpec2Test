// dafny-synthesis_task_id_18.dfy

method {:testEntry} RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && !(v[i] in s2)
  ensures forall i :: 0 <= i < |s1| ==> s1[i] in s2 || s1[i] in v
{
  var v': string := ['a', 'b', 'c'];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v'| <= i
    invariant forall k :: 0 <= k < |v'| ==> v'[k] in s1 && !(v'[k] in s2)
    invariant forall k :: 0 <= k < i ==> s1[k] in s2 || s1[k] in v'
  {
    if !(s1[i] in s2) {
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

// REPEAT 1 - TIME: 2.9949855 s

method {:test} Test2() {
var r0 := RemoveChars("\U{0002}", "aaaaaa\U{0002}a\0");
expect |r0| <= |"\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}" && !(r0[i] in "aaaaaa\U{0002}a\0");
expect forall i :: 0 <= i < |"\U{0002}"| ==> "\U{0002}"[i] in "aaaaaa\U{0002}a\0" || "\U{0002}"[i] in r0;
}
method {:test} Test3() {
var r0 := RemoveChars("\U{0002}\0", "\U{0002}");
expect |r0| <= |"\U{0002}\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0" && !(r0[i] in "\U{0002}");
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "\U{0002}" || "\U{0002}\0"[i] in r0;
}

// REPEAT 2 - TIME: 4.6237455 s

method {:test} Test4() {
var r0 := RemoveChars("\0aaaaaaaaaaa\0", "\0");
expect |r0| <= |"\0aaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0aaaaaaaaaaa\0" && !(r0[i] in "\0");
expect forall i :: 0 <= i < |"\0aaaaaaaaaaa\0"| ==> "\0aaaaaaaaaaa\0"[i] in "\0" || "\0aaaaaaaaaaa\0"[i] in r0;
}
method {:test} Test5() {
var r0 := RemoveChars("\U{0004}\0a", "\U{0004}\U{0002}");
expect |r0| <= |"\U{0004}\0a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\0a" && !(r0[i] in "\U{0004}\U{0002}");
expect forall i :: 0 <= i < |"\U{0004}\0a"| ==> "\U{0004}\0a"[i] in "\U{0004}\U{0002}" || "\U{0004}\0a"[i] in r0;
}

// REPEAT 3 - TIME: 6.0305777 s

method {:test} Test6() {
var r0 := RemoveChars("\U{0002}aaaaa\U{0006}\U{0008}", "\U{0004}a\U{0006}aaaaaaaaa\U{0008}aa\0\U{0002}");
expect |r0| <= |"\U{0002}aaaaa\U{0006}\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}aaaaa\U{0006}\U{0008}" && !(r0[i] in "\U{0004}a\U{0006}aaaaaaaaa\U{0008}aa\0\U{0002}");
expect forall i :: 0 <= i < |"\U{0002}aaaaa\U{0006}\U{0008}"| ==> "\U{0002}aaaaa\U{0006}\U{0008}"[i] in "\U{0004}a\U{0006}aaaaaaaaa\U{0008}aa\0\U{0002}" || "\U{0002}aaaaa\U{0006}\U{0008}"[i] in r0;
}
method {:test} Test7() {
var r0 := RemoveChars("a\0aa", "aaaaaaaaaa");
expect |r0| <= |"a\0aa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aa" && !(r0[i] in "aaaaaaaaaa");
expect forall i :: 0 <= i < |"a\0aa"| ==> "a\0aa"[i] in "aaaaaaaaaa" || "a\0aa"[i] in r0;
}

// REPEAT 4 - TIME: 7.6600522 s

method {:test} Test8() {
var r0 := RemoveChars("aaa\U{0006}aaa\U{0002}a\U{0008}", "aaa\U{0008}aaa\0a\U{0004}\U{0002}a\U{0006}aaa\n\U{000C}");
expect |r0| <= |"aaa\U{0006}aaa\U{0002}a\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\U{0006}aaa\U{0002}a\U{0008}" && !(r0[i] in "aaa\U{0008}aaa\0a\U{0004}\U{0002}a\U{0006}aaa\n\U{000C}");
expect forall i :: 0 <= i < |"aaa\U{0006}aaa\U{0002}a\U{0008}"| ==> "aaa\U{0006}aaa\U{0002}a\U{0008}"[i] in "aaa\U{0008}aaa\0a\U{0004}\U{0002}a\U{0006}aaa\n\U{000C}" || "aaa\U{0006}aaa\U{0002}a\U{0008}"[i] in r0;
}
method {:test} Test9() {
var r0 := RemoveChars("a\0aa\U{0006}\U{0002}", "\U{0008}a\U{0004}");
expect |r0| <= |"a\0aa\U{0006}\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aa\U{0006}\U{0002}" && !(r0[i] in "\U{0008}a\U{0004}");
expect forall i :: 0 <= i < |"a\0aa\U{0006}\U{0002}"| ==> "a\0aa\U{0006}\U{0002}"[i] in "\U{0008}a\U{0004}" || "a\0aa\U{0006}\U{0002}"[i] in r0;
}

// REPEAT 5 - TIME: 8.9481203 s

method {:test} Test10() {
var r0 := RemoveChars("\U{0002}aa\U{0006}\U{0008}aaaaaa", "\0aaa\U{0008}\U{0006}a\U{0004}aaaaaaaa\n\U{0002}a");
expect |r0| <= |"\U{0002}aa\U{0006}\U{0008}aaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}aa\U{0006}\U{0008}aaaaaa" && !(r0[i] in "\0aaa\U{0008}\U{0006}a\U{0004}aaaaaaaa\n\U{0002}a");
expect forall i :: 0 <= i < |"\U{0002}aa\U{0006}\U{0008}aaaaaa"| ==> "\U{0002}aa\U{0006}\U{0008}aaaaaa"[i] in "\0aaa\U{0008}\U{0006}a\U{0004}aaaaaaaa\n\U{0002}a" || "\U{0002}aa\U{0006}\U{0008}aaaaaa"[i] in r0;
}
method {:test} Test11() {
var r0 := RemoveChars("a\0aaaaaaaaa", "aaaa");
expect |r0| <= |"a\0aaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaa" && !(r0[i] in "aaaa");
expect forall i :: 0 <= i < |"a\0aaaaaaaaa"| ==> "a\0aaaaaaaaa"[i] in "aaaa" || "a\0aaaaaaaaa"[i] in r0;
}

// REPEAT 6 - TIME: 10.0830495 s

method {:test} Test12() {
var r0 := RemoveChars("aaa\0aaaaa\0aa", "aaaaa\0aaaaaaaaa\U{0002}aaa\U{0004}");
expect |r0| <= |"aaa\0aaaaa\0aa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\0aaaaa\0aa" && !(r0[i] in "aaaaa\0aaaaaaaaa\U{0002}aaa\U{0004}");
expect forall i :: 0 <= i < |"aaa\0aaaaa\0aa"| ==> "aaa\0aaaaa\0aa"[i] in "aaaaa\0aaaaaaaaa\U{0002}aaa\U{0004}" || "aaa\0aaaaa\0aa"[i] in r0;
}
method {:test} Test13() {
var r0 := RemoveChars("a\0aaaaaaa\U{0004}aaa\n", "aaaaa\naaa\U{0002}\U{0006}aaaaaa\U{0004}a\U{0008}");
expect |r0| <= |"a\0aaaaaaa\U{0004}aaa\n"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaa\U{0004}aaa\n" && !(r0[i] in "aaaaa\naaa\U{0002}\U{0006}aaaaaa\U{0004}a\U{0008}");
expect forall i :: 0 <= i < |"a\0aaaaaaa\U{0004}aaa\n"| ==> "a\0aaaaaaa\U{0004}aaa\n"[i] in "aaaaa\naaa\U{0002}\U{0006}aaaaaa\U{0004}a\U{0008}" || "a\0aaaaaaa\U{0004}aaa\n"[i] in r0;
}

// REPEAT 7 - TIME: 11.1425391 s

method {:test} Test14() {
var r0 := RemoveChars("aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaa\0aaaa\U{0004}aaaaaaa\U{0002}");
expect |r0| <= |"aaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaa" && !(r0[i] in "aaaaaaaaaaaaaaa\0aaaa\U{0004}aaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaa"[i] in "aaaaaaaaaaaaaaa\0aaaa\U{0004}aaaaaaa\U{0002}" || "aaaaaaaaaaaaaaa"[i] in r0;
}
method {:test} Test15() {
var r0 := RemoveChars("a\0aaaaaaaaaaaaa", "aaaaa");
expect |r0| <= |"a\0aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaaaa" && !(r0[i] in "aaaaa");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaa"| ==> "a\0aaaaaaaaaaaaa"[i] in "aaaaa" || "a\0aaaaaaaaaaaaa"[i] in r0;
}

// REPEAT 8 - TIME: 12.1858755 s

method {:test} Test16() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "aaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "aaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}" || "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}
method {:test} Test17() {
var r0 := RemoveChars("a\0aaaaaaaaaaa\U{0004}a\U{0006}", "aaaaa\U{0002}aaaaaaaaaaaaaa\U{0008}aaaa\naaa\U{000C}");
expect |r0| <= |"a\0aaaaaaaaaaa\U{0004}a\U{0006}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaa\U{0004}a\U{0006}" && !(r0[i] in "aaaaa\U{0002}aaaaaaaaaaaaaa\U{0008}aaaa\naaa\U{000C}");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaa\U{0004}a\U{0006}"| ==> "a\0aaaaaaaaaaa\U{0004}a\U{0006}"[i] in "aaaaa\U{0002}aaaaaaaaaaaaaa\U{0008}aaaa\naaa\U{000C}" || "a\0aaaaaaaaaaa\U{0004}a\U{0006}"[i] in r0;
}

// REPEAT 9 - TIME: 13.407659 s

method {:test} Test18() {
var r0 := RemoveChars("aaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaaaa\U{0004}a", "\0aaaa\U{0002}a\U{0004}aaaaaaaaaaa\U{0006}\U{0008}aaaaaaaa\n");
expect |r0| <= |"aaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaaaa\U{0004}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaaaa\U{0004}a" && !(r0[i] in "\0aaaa\U{0002}a\U{0004}aaaaaaaaaaa\U{0006}\U{0008}aaaaaaaa\n");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaaaa\U{0004}a"| ==> "aaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaaaa\U{0004}a"[i] in "\0aaaa\U{0002}a\U{0004}aaaaaaaaaaa\U{0006}\U{0008}aaaaaaaa\n" || "aaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaaaa\U{0004}a"[i] in r0;
}
method {:test} Test19() {
var r0 := RemoveChars("aaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaaaa\U{0004}a\0", "\U{0010}\U{0004}aaa\U{0002}aaaa\U{0006}aaaaaaaa\n\U{000C}aa\U{0008}aaa\U{000E}a");
expect |r0| <= |"aaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaaaa\U{0004}a\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaaaa\U{0004}a\0" && !(r0[i] in "\U{0010}\U{0004}aaa\U{0002}aaaa\U{0006}aaaaaaaa\n\U{000C}aa\U{0008}aaa\U{000E}a");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaaaa\U{0004}a\0"| ==> "aaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaaaa\U{0004}a\0"[i] in "\U{0010}\U{0004}aaa\U{0002}aaaa\U{0006}aaaaaaaa\n\U{000C}aa\U{0008}aaa\U{000E}a" || "aaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaaaa\U{0004}a\0"[i] in r0;
}

// REPEAT 10 - TIME: 14.6914722 s
