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

method {:test} Test5() {
var r0 := RemoveChars("a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}", "aaaaa\U{0006}aaaaaa\U{0002}\0aa\U{0004}aaaaa\U{0008}a\n");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}" && !(r0[i] in "aaaaa\U{0006}aaaaaa\U{0002}\0aa\U{0004}aaaaa\U{0008}a\n");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"| ==> "a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"[i] in "aaaaa\U{0006}aaaaaa\U{0002}\0aa\U{0004}aaaaa\U{0008}a\n" || "a\0aaaaaaaaaaaaaaaaaa\U{0006}\U{0002}\U{0008}"[i] in r0;
}

// REPEAT 6 - TIME: 8.3839041 s
