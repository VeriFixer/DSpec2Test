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

method {:test} Test15() {
var r0 := ReplaceChars("\0aa\0", '\U{0001}', '\0');
expect |r0| == |"\0aa\0"|;
expect forall i :: 0 <= i < |"\0aa\0"| ==> ("\0aa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aa\0"[i] != '\U{0001}' ==> r0[i] == "\0aa\0"[i]);
}
method {:test} Test16() {
var r0 := ReplaceChars("a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n", '\U{0001}', '\0');
expect |r0| == |"a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"|;
expect forall i :: 0 <= i < |"a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"| ==> ("a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"[i] != '\U{0001}' ==> r0[i] == "a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"[i]);
}
method {:test} Test17() {
var r0 := ReplaceChars("\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a", '\U{0001}', '\0');
expect |r0| == |"\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"|;
expect forall i :: 0 <= i < |"\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"| ==> ("\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"[i] != '\U{0001}' ==> r0[i] == "\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"[i]);
}

// REPEAT 6 - TIME: 12.0384769 s
