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


method {:test} Test0() {
var r0 := RemoveChars("a", "");
expect |r0| <= |"a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a" && !(r0[i] in "");
expect forall i :: 0 <= i < |"a"| ==> "a"[i] in "" || "a"[i] in r0;
}

// REPEAT 1 - TIME: 3.1485507 s

method {:test} Test1() {
var r0 := RemoveChars("a\0", "\0");
expect |r0| <= |"a\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0" && !(r0[i] in "\0");
expect forall i :: 0 <= i < |"a\0"| ==> "a\0"[i] in "\0" || "a\0"[i] in r0;
}

// REPEAT 2 - TIME: 4.3453263 s

method {:test} Test2() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0002}", "\0\U{0002}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0002}" && !(r0[i] in "\0\U{0002}");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0002}"| ==> "aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0002}"[i] in "\0\U{0002}" || "aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0002}"[i] in r0;
}

// REPEAT 3 - TIME: 5.3615135 s

method {:test} Test3() {
var r0 := RemoveChars("\U{0006}aaaaaaaaaaaaaaaa\U{0006}a\U{0006}", "\0\U{0002}a\U{0004}");
expect |r0| <= |"\U{0006}aaaaaaaaaaaaaaaa\U{0006}a\U{0006}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0006}aaaaaaaaaaaaaaaa\U{0006}a\U{0006}" && !(r0[i] in "\0\U{0002}a\U{0004}");
expect forall i :: 0 <= i < |"\U{0006}aaaaaaaaaaaaaaaa\U{0006}a\U{0006}"| ==> "\U{0006}aaaaaaaaaaaaaaaa\U{0006}a\U{0006}"[i] in "\0\U{0002}a\U{0004}" || "\U{0006}aaaaaaaaaaaaaaaa\U{0006}a\U{0006}"[i] in r0;
}

// REPEAT 4 - TIME: 6.4731081 s

method {:test} Test4() {
var r0 := RemoveChars("aa\U{0004}", "a\U{0002}aa\0aaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| <= |"aa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aa\U{0004}" && !(r0[i] in "a\U{0002}aa\0aaaaaaaaaaaaaaaaaa\U{0004}");
expect forall i :: 0 <= i < |"aa\U{0004}"| ==> "aa\U{0004}"[i] in "a\U{0002}aa\0aaaaaaaaaaaaaaaaaa\U{0004}" || "aa\U{0004}"[i] in r0;
}

// REPEAT 5 - TIME: 7.493824 s

method {:test} Test5() {
var r0 := RemoveChars("a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}", "aaaaa\U{0006}aaaaaa\U{0002}\0aa\U{0004}aaaaa\U{0008}a\n");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}" && !(r0[i] in "aaaaa\U{0006}aaaaaa\U{0002}\0aa\U{0004}aaaaa\U{0008}a\n");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"| ==> "a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"[i] in "aaaaa\U{0006}aaaaaa\U{0002}\0aa\U{0004}aaaaa\U{0008}a\n" || "a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"[i] in r0;
}

// REPEAT 6 - TIME: 8.3839041 s

method {:test} Test6() {
var r0 := RemoveChars("\U{0008}a\U{0004}aaaaaaa\naaaaaaaaa\U{000E}", "\U{0006}\U{0002}aa\0\naaaa\U{000E}a\U{0008}aaaa\U{0004}a\U{000C}");
expect |r0| <= |"\U{0008}a\U{0004}aaaaaaa\naaaaaaaaa\U{000E}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0008}a\U{0004}aaaaaaa\naaaaaaaaa\U{000E}" && !(r0[i] in "\U{0006}\U{0002}aa\0\naaaa\U{000E}a\U{0008}aaaa\U{0004}a\U{000C}");
expect forall i :: 0 <= i < |"\U{0008}a\U{0004}aaaaaaa\naaaaaaaaa\U{000E}"| ==> "\U{0008}a\U{0004}aaaaaaa\naaaaaaaaa\U{000E}"[i] in "\U{0006}\U{0002}aa\0\naaaa\U{000E}a\U{0008}aaaa\U{0004}a\U{000C}" || "\U{0008}a\U{0004}aaaaaaa\naaaaaaaaa\U{000E}"[i] in r0;
}

// REPEAT 7 - TIME: 9.2504425 s

method {:test} Test7() {
var r0 := RemoveChars("a\0aaaaaaaaaaa\0aaaaaa\0\0a\0", "\U{0004}aaa\U{0002}");
expect |r0| <= |"a\0aaaaaaaaaaa\0aaaaaa\0\0a\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaa\0aaaaaa\0\0a\0" && !(r0[i] in "\U{0004}aaa\U{0002}");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaa\0aaaaaa\0\0a\0"| ==> "a\0aaaaaaaaaaa\0aaaaaa\0\0a\0"[i] in "\U{0004}aaa\U{0002}" || "a\0aaaaaaaaaaa\0aaaaaa\0\0a\0"[i] in r0;
}

// REPEAT 8 - TIME: 10.1188927 s

method {:test} Test8() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaa\0a\U{0004}\U{0004}a", "\U{0002}\0aa\U{0006}\U{0004}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaa\0a\U{0004}\U{0004}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaa\0a\U{0004}\U{0004}a" && !(r0[i] in "\U{0002}\0aa\U{0006}\U{0004}");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\0a\U{0004}\U{0004}a"| ==> "aaaaaaaaaaaaaaaaaaaa\0a\U{0004}\U{0004}a"[i] in "\U{0002}\0aa\U{0006}\U{0004}" || "aaaaaaaaaaaaaaaaaaaa\0a\U{0004}\U{0004}a"[i] in r0;
}

// REPEAT 9 - TIME: 10.9730906 s

method {:test} Test9() {
var r0 := RemoveChars("\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}", "\U{0010}\U{0002}\n\U{0004}aaa\0\U{000C}\U{0008}aaaaa\U{0006}aaaa\U{000E}");
expect |r0| <= |"\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}" && !(r0[i] in "\U{0010}\U{0002}\n\U{0004}aaa\0\U{000C}\U{0008}aaaaa\U{0006}aaaa\U{000E}");
expect forall i :: 0 <= i < |"\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"| ==> "\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"[i] in "\U{0010}\U{0002}\n\U{0004}aaa\0\U{000C}\U{0008}aaaaa\U{0006}aaaa\U{000E}" || "\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"[i] in r0;
}

// REPEAT 10 - TIME: 11.8344903 s
