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
    if false {
      s' := s' + [ch];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("a ", '\0');
expect |r0| == |"a "|;
expect forall i :: 0 <= i < |"a "| ==> ("a "[i] == ' ' ==> r0[i] == '\0') && ("a "[i] != ' ' ==> r0[i] == "a "[i]);
}

// REPEAT 2 - TIME: 3.5569164 s
