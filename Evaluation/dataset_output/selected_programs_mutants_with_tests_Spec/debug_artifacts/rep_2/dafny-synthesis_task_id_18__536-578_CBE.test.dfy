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
    v' := v' + [s1[i]];
  }
  return v';
}

method {:test} Test1() {
var r0 := RemoveChars("a\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0");
expect |r0| <= |"a\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\U{0002}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0");
expect forall i :: 0 <= i < |"a\U{0002}"| ==> "a\U{0002}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0" || "a\U{0002}"[i] in r0;
}

// REPEAT 2 - TIME: 3.515095 s
