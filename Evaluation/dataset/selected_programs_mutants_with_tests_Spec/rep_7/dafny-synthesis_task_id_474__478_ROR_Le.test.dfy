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

method {:test} Test6() {
var r0 := ReplaceChars("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"|;
expect forall i :: 0 <= i < |"aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"| ==> ("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i]);
}

// REPEAT 7 - TIME: 8.9838862 s
