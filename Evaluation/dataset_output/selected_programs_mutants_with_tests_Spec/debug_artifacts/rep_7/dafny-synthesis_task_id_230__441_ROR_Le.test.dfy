// dafny-synthesis_task_id_230.dfy

method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
  {
    if s[i] <= ' ' {
      s' := s' + [ch];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaaa ", '\0');
expect |r0| == |"  aaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"  aaaaaaaaaaa "| ==> ("  aaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaaa "[i] != ' ' ==> r0[i] == "  aaaaaaaaaaa "[i]);
}

// REPEAT 7 - TIME: 8.7008803 s
