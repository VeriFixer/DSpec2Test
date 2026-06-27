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
var r0 := ReplaceChars("aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"| ==> ("aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"[i]);
}
method {:test} Test16() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceChars("\0", '\0', '\0');
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> ("\0"[i] == '\0' ==> r0[i] == '\0') && ("\0"[i] != '\0' ==> r0[i] == "\0"[i]);
}

// REPEAT 6 - TIME: 11.8095745 s
