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

method {:test} Test9() {
var r0 := ReplaceChars("\0aaaaaa\0aaaa\0", '\U{0001}', '\0');
expect |r0| == |"\0aaaaaa\0aaaa\0"|;
expect forall i :: 0 <= i < |"\0aaaaaa\0aaaa\0"| ==> ("\0aaaaaa\0aaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaaaaa\0aaaa\0"[i] != '\U{0001}' ==> r0[i] == "\0aaaaaa\0aaaa\0"[i]);
}
method {:test} Test10() {
var r0 := ReplaceChars("\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}", '\U{0001}', '\0');
expect |r0| == |"\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"|;
expect forall i :: 0 <= i < |"\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"| ==> ("\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"[i] != '\U{0001}' ==> r0[i] == "\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceChars("\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"| ==> ("\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"[i]);
}

// REPEAT 4 - TIME: 8.3766831 s
