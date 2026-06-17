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
      v' := [s1[i]];
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

// REPEAT 1 - TIME: 2.6181036 s

method {:test} Test1() {
var r0 := RemoveChars("a\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0");
expect |r0| <= |"a\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\U{0002}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0");
expect forall i :: 0 <= i < |"a\U{0002}"| ==> "a\U{0002}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0" || "a\U{0002}"[i] in r0;
}

// REPEAT 2 - TIME: 3.515095 s

method {:test} Test2() {
var r0 := RemoveChars("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\0");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "\0");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "\0" || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 3 - TIME: 4.5792835 s

method {:test} Test3() {
var r0 := RemoveChars("\U{0002}a", "a\0");
expect |r0| <= |"\U{0002}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}a" && !(r0[i] in "a\0");
expect forall i :: 0 <= i < |"\U{0002}a"| ==> "\U{0002}a"[i] in "a\0" || "\U{0002}a"[i] in r0;
}

// REPEAT 4 - TIME: 5.629324 s

method {:test} Test4() {
var r0 := RemoveChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0002}\0");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}" && !(r0[i] in "\U{0002}\0");
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "\U{0002}\0" || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in r0;
}

// REPEAT 5 - TIME: 6.7729002 s

method {:test} Test5() {
var r0 := RemoveChars("\0\0a", "\U{0002}aa");
expect |r0| <= |"\0\0a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0\0a" && !(r0[i] in "\U{0002}aa");
expect forall i :: 0 <= i < |"\0\0a"| ==> "\0\0a"[i] in "\U{0002}aa" || "\0\0a"[i] in r0;
}

// REPEAT 6 - TIME: 7.7742398 s

method {:test} Test6() {
var r0 := RemoveChars("\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0008}\0a\U{0004}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\n");
expect |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}" && !(r0[i] in "\U{0008}\0a\U{0004}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\n");
expect forall i :: 0 <= i < |"\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "\U{0008}\0a\U{0004}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\n" || "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"[i] in r0;
}

// REPEAT 7 - TIME: 8.5441462 s

method {:test} Test7() {
var r0 := RemoveChars("\U{0002}\U{0002}a", "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| <= |"\U{0002}\U{0002}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\U{0002}a" && !(r0[i] in "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect forall i :: 0 <= i < |"\U{0002}\U{0002}a"| ==> "\U{0002}\U{0002}a"[i] in "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}" || "\U{0002}\U{0002}a"[i] in r0;
}

// REPEAT 8 - TIME: 9.4633345 s

method {:test} Test8() {
var r0 := RemoveChars("\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}", "\U{0004}aaaaaaaaaaaa\U{0002}aaaaaa\U{000C}aaaaaaaa\U{0006}aaaaaa\U{0008}aa\naaaaaaa\0");
expect |r0| <= |"\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}" && !(r0[i] in "\U{0004}aaaaaaaaaaaa\U{0002}aaaaaa\U{000C}aaaaaaaa\U{0006}aaaaaa\U{0008}aa\naaaaaaa\0");
expect forall i :: 0 <= i < |"\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"| ==> "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"[i] in "\U{0004}aaaaaaaaaaaa\U{0002}aaaaaa\U{000C}aaaaaaaa\U{0006}aaaaaa\U{0008}aa\naaaaaaa\0" || "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"[i] in r0;
}

// REPEAT 9 - TIME: 10.3610682 s

method {:test} Test9() {
var r0 := RemoveChars("\U{0006}a\U{0002}\U{0002}", "\U{0004}\0\U{0002}\U{0008}a\U{0006}");
expect |r0| <= |"\U{0006}a\U{0002}\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0006}a\U{0002}\U{0002}" && !(r0[i] in "\U{0004}\0\U{0002}\U{0008}a\U{0006}");
expect forall i :: 0 <= i < |"\U{0006}a\U{0002}\U{0002}"| ==> "\U{0006}a\U{0002}\U{0002}"[i] in "\U{0004}\0\U{0002}\U{0008}a\U{0006}" || "\U{0006}a\U{0002}\U{0002}"[i] in r0;
}

// REPEAT 10 - TIME: 11.1458331 s
