// dafny-synthesis_task_id_732.dfy

predicate IsSpaceCommaDot(c: char)
{
  c == ' ' || c == ',' || c == '.'
}

method {:testEntry} ReplaceWithColon(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
  {
    s' := s' + [s[i]];
  }
  return s';
}

method {:test} Test3() {
var r0 := ReplaceWithColon("a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |"a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> (IsSpaceCommaDot("a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == "a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]);
}

// REPEAT 4 - TIME: 6.3628136 s
