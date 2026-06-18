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

// REPEAT 1 - TIME: 8.1745871 s

method {:test} Test13() {
var r0 := RemoveChars("aa\0", "\U{0002}\0");
expect |r0| <= |"aa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aa\0" && !(r0[i] in "\U{0002}\0");
expect forall i :: 0 <= i < |"aa\0"| ==> "aa\0"[i] in "\U{0002}\0" || "aa\0"[i] in r0;
}

// REPEAT 2 - TIME: 9.0024274 s

method {:test} Test14() {
var r0 := RemoveChars("a\0a\U{0002}aaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0002}", "a\0a");
expect |r0| <= |"a\0a\U{0002}aaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0a\U{0002}aaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0002}" && !(r0[i] in "a\0a");
expect forall i :: 0 <= i < |"a\0a\U{0002}aaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "a\0a\U{0002}aaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "a\0a" || "a\0a\U{0002}aaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0002}"[i] in r0;
}

// REPEAT 3 - TIME: 9.629386 s

method {:test} Test15() {
var r0 := RemoveChars("\U{0006}\U{0004}", "a\U{0002}a\U{0008}aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\0a\n");
expect |r0| <= |"\U{0006}\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0006}\U{0004}" && !(r0[i] in "a\U{0002}a\U{0008}aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\0a\n");
expect forall i :: 0 <= i < |"\U{0006}\U{0004}"| ==> "\U{0006}\U{0004}"[i] in "a\U{0002}a\U{0008}aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\0a\n" || "\U{0006}\U{0004}"[i] in r0;
}

// REPEAT 4 - TIME: 10.484108 s

method {:test} Test16() {
var r0 := RemoveChars("\U{0004}\U{0004}\U{0004}\U{0004}", "\U{0006}\U{0002}a\0");
expect |r0| <= |"\U{0004}\U{0004}\U{0004}\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\U{0004}\U{0004}\U{0004}" && !(r0[i] in "\U{0006}\U{0002}a\0");
expect forall i :: 0 <= i < |"\U{0004}\U{0004}\U{0004}\U{0004}"| ==> "\U{0004}\U{0004}\U{0004}\U{0004}"[i] in "\U{0006}\U{0002}a\0" || "\U{0004}\U{0004}\U{0004}\U{0004}"[i] in r0;
}

// REPEAT 5 - TIME: 11.1749912 s

method {:test} Test17() {
var r0 := RemoveChars("\0\0a\0aaaaaaa\0aaaa\0aaaaaaaaaaaa\0", "\U{0006}aa\U{0004}\U{0002}");
expect |r0| <= |"\0\0a\0aaaaaaa\0aaaa\0aaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0\0a\0aaaaaaa\0aaaa\0aaaaaaaaaaaa\0" && !(r0[i] in "\U{0006}aa\U{0004}\U{0002}");
expect forall i :: 0 <= i < |"\0\0a\0aaaaaaa\0aaaa\0aaaaaaaaaaaa\0"| ==> "\0\0a\0aaaaaaa\0aaaa\0aaaaaaaaaaaa\0"[i] in "\U{0006}aa\U{0004}\U{0002}" || "\0\0a\0aaaaaaa\0aaaa\0aaaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 6 - TIME: 11.9544604 s

method {:test} Test18() {
var r0 := RemoveChars("\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}\U{0004}\0");
expect |r0| <= |"\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "\U{0002}\U{0004}\0");
expect forall i :: 0 <= i < |"\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "\U{0002}\U{0004}\0" || "\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}

// REPEAT 7 - TIME: 12.7270784 s

method {:test} Test19() {
var r0 := RemoveChars("\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n", "\U{0006}\0a\U{0002}\U{0004}\U{0008}");
expect |r0| <= |"\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n" && !(r0[i] in "\U{0006}\0a\U{0002}\U{0004}\U{0008}");
expect forall i :: 0 <= i < |"\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"| ==> "\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"[i] in "\U{0006}\0a\U{0002}\U{0004}\U{0008}" || "\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"[i] in r0;
}

// REPEAT 8 - TIME: 13.5498845 s

method {:test} Test20() {
var r0 := RemoveChars("\U{0008}\U{0008}aaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaa", "\n\U{0008}\U{0002}a\U{0006}\0\U{0004}");
expect |r0| <= |"\U{0008}\U{0008}aaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0008}\U{0008}aaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaa" && !(r0[i] in "\n\U{0008}\U{0002}a\U{0006}\0\U{0004}");
expect forall i :: 0 <= i < |"\U{0008}\U{0008}aaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaa"| ==> "\U{0008}\U{0008}aaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaa"[i] in "\n\U{0008}\U{0002}a\U{0006}\0\U{0004}" || "\U{0008}\U{0008}aaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaa"[i] in r0;
}

// REPEAT 9 - TIME: 14.3134722 s

method {:test} Test21() {
var r0 := RemoveChars("\U{0002}\U{0002}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0004}a\n", "\U{0008}\na\U{0006}\U{0004}\U{0002}a\0");
expect |r0| <= |"\U{0002}\U{0002}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0004}a\n"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\U{0002}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0004}a\n" && !(r0[i] in "\U{0008}\na\U{0006}\U{0004}\U{0002}a\0");
expect forall i :: 0 <= i < |"\U{0002}\U{0002}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0004}a\n"| ==> "\U{0002}\U{0002}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0004}a\n"[i] in "\U{0008}\na\U{0006}\U{0004}\U{0002}a\0" || "\U{0002}\U{0002}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0004}a\n"[i] in r0;
}

// REPEAT 10 - TIME: 15.1430382 s
