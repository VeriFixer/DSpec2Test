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
    if IsSpaceCommaDot(s[i]) {
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test4() {
var r0 := ReplaceWithColon("aaa");
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> (IsSpaceCommaDot("aaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa"[i]) ==> r0[i] == "aaa"[i]);
}
method {:test} Test5() {
var r0 := ReplaceWithColon(" ");
expect |r0| == |" "|;
expect forall i :: 0 <= i < |" "| ==> (IsSpaceCommaDot(" "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" "[i]) ==> r0[i] == " "[i]);
}
method {:test} Test7() {
var r0 := ReplaceWithColon(" aaaaa\0");
expect |r0| == |" aaaaa\0"|;
expect forall i :: 0 <= i < |" aaaaa\0"| ==> (IsSpaceCommaDot(" aaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaa\0"[i]) ==> r0[i] == " aaaaa\0"[i]);
}

// REPEAT 2 - TIME: 6.6329949 s
