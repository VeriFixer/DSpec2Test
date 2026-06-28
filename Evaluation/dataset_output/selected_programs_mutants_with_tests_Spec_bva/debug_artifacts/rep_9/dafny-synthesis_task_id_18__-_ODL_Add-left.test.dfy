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

method {:test} Test20() {
var r0 := RemoveChars("\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a", "\U{000C}\U{0006}\n\U{0004}aa\0a\U{0002}\U{0008}aaa\U{000E}");
expect |r0| <= |"\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a" && !(r0[i] in "\U{000C}\U{0006}\n\U{0004}aa\0a\U{0002}\U{0008}aaa\U{000E}");
expect forall i :: 0 <= i < |"\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"| ==> "\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"[i] in "\U{000C}\U{0006}\n\U{0004}aa\0a\U{0002}\U{0008}aaa\U{000E}" || "\U{000E}\0aa\U{0002}\U{0002}aa\U{0006}aaa\n\U{0006}a"[i] in r0;
}

// REPEAT 9 - TIME: 19.128694 s
