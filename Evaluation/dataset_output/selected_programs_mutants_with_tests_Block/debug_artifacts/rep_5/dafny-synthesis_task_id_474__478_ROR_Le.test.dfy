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

method {:test} Test12() {
var r0 := ReplaceChars("aa\0aaaaaaaaa\0aaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aa\0aaaaaaaaa\0aaaaaaa\0"|;
expect forall i :: 0 <= i < |"aa\0aaaaaaaaa\0aaaaaaa\0"| ==> ("aa\0aaaaaaaaa\0aaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\0aaaaaaaaa\0aaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aa\0aaaaaaaaa\0aaaaaaa\0"[i]);
}
method {:test} Test13() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaa"| ==> ("\U{0001}aaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 9.2361793 s
