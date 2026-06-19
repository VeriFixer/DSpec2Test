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

method {:test} Test19() {
var r0 := RemoveChars("\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n", "\U{0006}\0a\U{0002}\U{0004}\U{0008}");
expect |r0| <= |"\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n" && !(r0[i] in "\U{0006}\0a\U{0002}\U{0004}\U{0008}");
expect forall i :: 0 <= i < |"\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"| ==> "\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"[i] in "\U{0006}\0a\U{0002}\U{0004}\U{0008}" || "\naaaa\naaa\naaaaaaaaaaa\naaaaaaa\n"[i] in r0;
}

// REPEAT 8 - TIME: 13.5725028 s
