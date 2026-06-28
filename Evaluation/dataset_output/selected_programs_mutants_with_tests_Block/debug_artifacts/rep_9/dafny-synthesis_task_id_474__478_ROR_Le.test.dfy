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

method {:test} Test24() {
var r0 := ReplaceChars("\0aaaaaaaaaaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaa\0"| ==> ("\0aaaaaaaaaaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaaaaaaaaaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test25() {
var r0 := ReplaceChars("a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa", '\U{0001}', '\0');
expect |r0| == |"a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"|;
expect forall i :: 0 <= i < |"a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"| ==> ("a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"[i] != '\U{0001}' ==> r0[i] == "a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"[i]);
}
method {:test} Test26() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"| ==> ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"[i]);
}

// REPEAT 9 - TIME: 16.8715415 s
