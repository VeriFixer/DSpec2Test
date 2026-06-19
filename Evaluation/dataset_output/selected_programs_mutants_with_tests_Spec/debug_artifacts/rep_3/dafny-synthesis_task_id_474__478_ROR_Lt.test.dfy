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
    if s[i] < oldChar {
      s' := s' + [newChar];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test2() {
var r0 := ReplaceChars("aaaa\0aaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaa\0aaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaa\0aaaaaaaaaaaaaaaa\U{0001}"| ==> ("aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 4.5108265 s
