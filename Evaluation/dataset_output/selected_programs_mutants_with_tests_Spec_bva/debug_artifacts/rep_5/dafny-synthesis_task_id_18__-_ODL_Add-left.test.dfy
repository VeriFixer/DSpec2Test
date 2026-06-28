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

method {:test} Test16() {
var r0 := RemoveChars("\naaaaaaaa\U{0002}aa\U{0004}", "\U{0008}\0\naaa\U{0002}aaaaaaaa\U{0004}\U{0006}");
expect |r0| <= |"\naaaaaaaa\U{0002}aa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\naaaaaaaa\U{0002}aa\U{0004}" && !(r0[i] in "\U{0008}\0\naaa\U{0002}aaaaaaaa\U{0004}\U{0006}");
expect forall i :: 0 <= i < |"\naaaaaaaa\U{0002}aa\U{0004}"| ==> "\naaaaaaaa\U{0002}aa\U{0004}"[i] in "\U{0008}\0\naaa\U{0002}aaaaaaaa\U{0004}\U{0006}" || "\naaaaaaaa\U{0002}aa\U{0004}"[i] in r0;
}

// REPEAT 5 - TIME: 15.353995 s
