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

method {:test} Test21() {
var r0 := ReplaceChars("aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"| ==> ("aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test22() {
var r0 := ReplaceChars("\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"| ==> ("\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"[i]);
}
method {:test} Test23() {
var r0 := ReplaceChars("aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}", '\U{0001}', '\0');
expect |r0| == |"aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"|;
expect forall i :: 0 <= i < |"aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"| ==> ("aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"[i] != '\U{0001}' ==> r0[i] == "aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"[i]);
}

// REPEAT 8 - TIME: 15.1374727 s
