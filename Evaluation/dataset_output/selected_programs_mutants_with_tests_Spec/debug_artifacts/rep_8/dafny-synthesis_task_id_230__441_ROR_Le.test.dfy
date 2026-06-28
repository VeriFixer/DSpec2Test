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

method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a", '\0');
expect |r0| == |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"|;
expect forall i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"| ==> ("\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"[i] != ' ' ==> r0[i] == "\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"[i]);
}

// REPEAT 8 - TIME: 9.4459709 s
