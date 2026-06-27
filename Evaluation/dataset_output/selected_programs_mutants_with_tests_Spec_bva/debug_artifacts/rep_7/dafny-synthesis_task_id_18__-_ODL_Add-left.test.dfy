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

method {:test} Test18() {
var r0 := RemoveChars("\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}\U{0004}\0");
expect |r0| <= |"\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "\U{0002}\U{0004}\0");
expect forall i :: 0 <= i < |"\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "\U{0002}\U{0004}\0" || "\U{0004}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}

// REPEAT 7 - TIME: 12.8738218 s
