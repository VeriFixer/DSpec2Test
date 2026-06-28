// dafny-synthesis_task_id_474.dfy

method {:testEntry} ReplaceChars(s: string, oldChar: char, newChar: char)
    returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == oldChar ==> s'[k] == newChar) && (s[k] != oldChar ==> s'[k] == s[k])
  {
    if s[i] <= oldChar {
      s' := s' + [newChar];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test10() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaa\0a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaa\0a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaa\0a"| ==> ("aaaaaaaaaaaaaaaaaa\0a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaa\0a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaa\0a"[i]);
}

// REPEAT 2 - TIME: 10.5045239 s
