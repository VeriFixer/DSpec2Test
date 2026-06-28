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

method {:test} Test4() {
var r0 := RemoveChars("aa\U{0004}", "a\U{0002}aa\0aaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| <= |"aa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aa\U{0004}" && !(r0[i] in "a\U{0002}aa\0aaaaaaaaaaaaaaaaaa\U{0004}");
expect forall i :: 0 <= i < |"aa\U{0004}"| ==> "aa\U{0004}"[i] in "a\U{0002}aa\0aaaaaaaaaaaaaaaaaa\U{0004}" || "aa\U{0004}"[i] in r0;
}

// REPEAT 5 - TIME: 7.493824 s
