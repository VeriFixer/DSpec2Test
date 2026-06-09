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
var r0 := ReplaceChars("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test16() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceChars("aaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaaa\U{0001}a"| ==> ("aaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0001}a"[i]);
}

// REPEAT 6 - TIME: 10.9492203 s
