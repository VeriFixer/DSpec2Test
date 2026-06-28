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

method {:test} Test13() {
var r0 := ReplaceBlanksWithChar(" aaa", '\0');
expect |r0| == |" aaa"|;
expect forall i :: 0 <= i < |" aaa"| ==> (" aaa"[i] == ' ' ==> r0[i] == '\0') && (" aaa"[i] != ' ' ==> r0[i] == " aaa"[i]);
}

// REPEAT 5 - TIME: 12.8181271 s
