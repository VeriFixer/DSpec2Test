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

method {:test} Test11() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |"  aaaaaaaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"  aaaaaaaaaaaaaaaaa\U{0003}"| ==> ("  aaaaaaaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "  aaaaaaaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 3 - TIME: 8.5671787 s
