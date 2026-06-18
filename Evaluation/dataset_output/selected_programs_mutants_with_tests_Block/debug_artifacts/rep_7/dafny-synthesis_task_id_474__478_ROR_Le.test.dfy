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

method {:test} Test18() {
var r0 := ReplaceChars("\0a\0", '\U{0001}', '\0');
expect |r0| == |"\0a\0"|;
expect forall i :: 0 <= i < |"\0a\0"| ==> ("\0a\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\0"[i] != '\U{0001}' ==> r0[i] == "\0a\0"[i]);
}
method {:test} Test19() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaa\U{0002}aa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0002}aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0002}aa"| ==> ("aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i]);
}
method {:test} Test20() {
var r0 := ReplaceChars("aaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaa\U{0001}"| ==> ("aaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 7 - TIME: 13.072266 s
