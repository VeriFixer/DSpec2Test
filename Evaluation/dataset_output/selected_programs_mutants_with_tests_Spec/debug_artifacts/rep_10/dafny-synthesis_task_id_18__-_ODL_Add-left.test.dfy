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

method {:test} Test9() {
var r0 := RemoveChars("\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}", "\U{0010}\U{0002}\n\U{0004}aaa\0\U{000C}\U{0008}aaaaa\U{0006}aaaa\U{000E}");
expect |r0| <= |"\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}" && !(r0[i] in "\U{0010}\U{0002}\n\U{0004}aaa\0\U{000C}\U{0008}aaaaa\U{0006}aaaa\U{000E}");
expect forall i :: 0 <= i < |"\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"| ==> "\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"[i] in "\U{0010}\U{0002}\n\U{0004}aaa\0\U{000C}\U{0008}aaaaa\U{0006}aaaa\U{000E}" || "\U{000E}aaaaaa\U{0006}aaaaaaa\U{0006}aaaaa\n\U{000C}\U{000C}"[i] in r0;
}

// REPEAT 10 - TIME: 11.8344903 s
