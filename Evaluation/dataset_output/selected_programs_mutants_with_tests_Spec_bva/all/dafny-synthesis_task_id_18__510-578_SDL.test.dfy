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
var r0 := RemoveChars("", "");
expect |r0| <= |""|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "" && !(r0[i] in "");
expect forall i :: 0 <= i < |""| ==> ""[i] in "" || ""[i] in r0;
}
method {:test} Test3() {
var r0 := RemoveChars("aa", "");
expect |r0| <= |"aa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aa" && !(r0[i] in "");
expect forall i :: 0 <= i < |"aa"| ==> "aa"[i] in "" || "aa"[i] in r0;
}
method {:test} Test5() {
var r0 := RemoveChars("a", "a");
expect |r0| <= |"a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a" && !(r0[i] in "a");
expect forall i :: 0 <= i < |"a"| ==> "a"[i] in "a" || "a"[i] in r0;
}
method {:test} Test6() {
var r0 := RemoveChars("a", "aa");
expect |r0| <= |"a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a" && !(r0[i] in "aa");
expect forall i :: 0 <= i < |"a"| ==> "a"[i] in "aa" || "a"[i] in r0;
}

// REPEAT 1 - TIME: 10.5261194 s

method {:test} Test13() {
var r0 := RemoveChars("aaaaaaaaaaa\U{0002}aaaa\U{0004}", "\0\U{0004}\U{0002}");
expect |r0| <= |"aaaaaaaaaaa\U{0002}aaaa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaa\U{0002}aaaa\U{0004}" && !(r0[i] in "\0\U{0004}\U{0002}");
expect forall i :: 0 <= i < |"aaaaaaaaaaa\U{0002}aaaa\U{0004}"| ==> "aaaaaaaaaaa\U{0002}aaaa\U{0004}"[i] in "\0\U{0004}\U{0002}" || "aaaaaaaaaaa\U{0002}aaaa\U{0004}"[i] in r0;
}

// REPEAT 2 - TIME: 11.8645043 s

method {:test} Test14() {
var r0 := RemoveChars("\U{0004}\0a\0", "\U{0002}\0\U{0004}");
expect |r0| <= |"\U{0004}\0a\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\0a\0" && !(r0[i] in "\U{0002}\0\U{0004}");
expect forall i :: 0 <= i < |"\U{0004}\0a\0"| ==> "\U{0004}\0a\0"[i] in "\U{0002}\0\U{0004}" || "\U{0004}\0a\0"[i] in r0;
}

// REPEAT 3 - TIME: 12.8657095 s

method {:test} Test15() {
var r0 := RemoveChars("a\0a\U{0006}a", "\U{0004}\U{0002}aaa\U{0006}a\0a\U{0008}");
expect |r0| <= |"a\0a\U{0006}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0a\U{0006}a" && !(r0[i] in "\U{0004}\U{0002}aaa\U{0006}a\0a\U{0008}");
expect forall i :: 0 <= i < |"a\0a\U{0006}a"| ==> "a\0a\U{0006}a"[i] in "\U{0004}\U{0002}aaa\U{0006}a\0a\U{0008}" || "a\0a\U{0006}a"[i] in r0;
}

// REPEAT 4 - TIME: 14.1306102 s

method {:test} Test16() {
var r0 := RemoveChars("\naaaaaaaa\U{0002}aa\U{0004}", "\U{0008}\0\naaa\U{0002}aaaaaaaa\U{0004}\U{0006}");
expect |r0| <= |"\naaaaaaaa\U{0002}aa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\naaaaaaaa\U{0002}aa\U{0004}" && !(r0[i] in "\U{0008}\0\naaa\U{0002}aaaaaaaa\U{0004}\U{0006}");
expect forall i :: 0 <= i < |"\naaaaaaaa\U{0002}aa\U{0004}"| ==> "\naaaaaaaa\U{0002}aa\U{0004}"[i] in "\U{0008}\0\naaa\U{0002}aaaaaaaa\U{0004}\U{0006}" || "\naaaaaaaa\U{0002}aa\U{0004}"[i] in r0;
}

// REPEAT 5 - TIME: 15.353995 s

method {:test} Test17() {
var r0 := RemoveChars("\U{0004}\U{0004}\U{0004}", "\U{0006}a\0\U{0002}");
expect |r0| <= |"\U{0004}\U{0004}\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\U{0004}\U{0004}" && !(r0[i] in "\U{0006}a\0\U{0002}");
expect forall i :: 0 <= i < |"\U{0004}\U{0004}\U{0004}"| ==> "\U{0004}\U{0004}\U{0004}"[i] in "\U{0006}a\0\U{0002}" || "\U{0004}\U{0004}\U{0004}"[i] in r0;
}

// REPEAT 6 - TIME: 16.2314731 s

method {:test} Test18() {
var r0 := RemoveChars("a\0aaa\U{0004}aa\U{0008}aaaa\U{000C}", "aa\U{0002}\U{000C}aa\0a\U{0006}a\U{0008}\U{0004}\n");
expect |r0| <= |"a\0aaa\U{0004}aa\U{0008}aaaa\U{000C}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaa\U{0004}aa\U{0008}aaaa\U{000C}" && !(r0[i] in "aa\U{0002}\U{000C}aa\0a\U{0006}a\U{0008}\U{0004}\n");
expect forall i :: 0 <= i < |"a\0aaa\U{0004}aa\U{0008}aaaa\U{000C}"| ==> "a\0aaa\U{0004}aa\U{0008}aaaa\U{000C}"[i] in "aa\U{0002}\U{000C}aa\0a\U{0006}a\U{0008}\U{0004}\n" || "a\0aaa\U{0004}aa\U{0008}aaaa\U{000C}"[i] in r0;
}

// REPEAT 7 - TIME: 17.2319896 s

method {:test} Test19() {
var r0 := RemoveChars("\U{0008}\0\U{0002}a\U{0006}\U{0008}", "\U{0002}\U{0008}\U{0006}\0\U{0004}");
expect |r0| <= |"\U{0008}\0\U{0002}a\U{0006}\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0008}\0\U{0002}a\U{0006}\U{0008}" && !(r0[i] in "\U{0002}\U{0008}\U{0006}\0\U{0004}");
expect forall i :: 0 <= i < |"\U{0008}\0\U{0002}a\U{0006}\U{0008}"| ==> "\U{0008}\0\U{0002}a\U{0006}\U{0008}"[i] in "\U{0002}\U{0008}\U{0006}\0\U{0004}" || "\U{0008}\0\U{0002}a\U{0006}\U{0008}"[i] in r0;
}

// REPEAT 8 - TIME: 18.1731977 s

method {:test} Test20() {
var r0 := RemoveChars("\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a", "\U{000C}\U{0006}\n\U{0004}aa\0a\U{0002}\U{0008}aaa\U{000E}");
expect |r0| <= |"\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a" && !(r0[i] in "\U{000C}\U{0006}\n\U{0004}aa\0a\U{0002}\U{0008}aaa\U{000E}");
expect forall i :: 0 <= i < |"\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"| ==> "\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"[i] in "\U{000C}\U{0006}\n\U{0004}aa\0a\U{0002}\U{0008}aaa\U{000E}" || "\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"[i] in r0;
}

// REPEAT 9 - TIME: 19.128694 s

method {:test} Test21() {
var r0 := RemoveChars("\U{0004}\U{0002}aaa\U{0006}\U{0006}aaaa\U{0004}", "\n\0\U{0006}\U{0002}\U{0008}\U{0004}");
expect |r0| <= |"\U{0004}\U{0002}aaa\U{0006}\U{0006}aaaa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\U{0002}aaa\U{0006}\U{0006}aaaa\U{0004}" && !(r0[i] in "\n\0\U{0006}\U{0002}\U{0008}\U{0004}");
expect forall i :: 0 <= i < |"\U{0004}\U{0002}aaa\U{0006}\U{0006}aaaa\U{0004}"| ==> "\U{0004}\U{0002}aaa\U{0006}\U{0006}aaaa\U{0004}"[i] in "\n\0\U{0006}\U{0002}\U{0008}\U{0004}" || "\U{0004}\U{0002}aaa\U{0006}\U{0006}aaaa\U{0004}"[i] in r0;
}

// REPEAT 10 - TIME: 20.1649208 s
