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

method {:test} Test5() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaa ");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa "| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaa "[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 6 - TIME: 8.7619084 s
