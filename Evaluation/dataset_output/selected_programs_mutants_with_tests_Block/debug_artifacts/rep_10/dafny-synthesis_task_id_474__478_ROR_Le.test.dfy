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

method {:test} Test27() {
var r0 := ReplaceChars("aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa", '\U{0001}', '\0');
expect |r0| == |"aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"|;
expect forall i :: 0 <= i < |"aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"| ==> ("aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"[i] != '\U{0001}' ==> r0[i] == "aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceChars("\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"|;
expect forall i :: 0 <= i < |"\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"| ==> ("\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"| ==> ("\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"[i]);
}

// REPEAT 10 - TIME: 17.6839142 s
