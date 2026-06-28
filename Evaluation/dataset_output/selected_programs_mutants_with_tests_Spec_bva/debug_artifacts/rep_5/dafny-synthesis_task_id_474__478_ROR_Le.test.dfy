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

method {:test} Test13() {
var r0 := ReplaceChars("aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"| ==> ("aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 13.2920852 s
