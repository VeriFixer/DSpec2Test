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
var r0 := ReplaceChars("aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"| ==> ("aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"[i]);
}
method {:test} Test25() {
var r0 := ReplaceChars("a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta", '\U{0001}', '\0');
expect |r0| == |"a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"|;
expect forall i :: 0 <= i < |"a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"| ==> ("a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"[i] != '\U{0001}' ==> r0[i] == "a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"[i]);
}
method {:test} Test26() {
var r0 := ReplaceChars("\0aaa", '\0', '\0');
expect |r0| == |"\0aaa"|;
expect forall i :: 0 <= i < |"\0aaa"| ==> ("\0aaa"[i] == '\0' ==> r0[i] == '\0') && ("\0aaa"[i] != '\0' ==> r0[i] == "\0aaa"[i]);
}

// REPEAT 9 - TIME: 16.2785801 s
