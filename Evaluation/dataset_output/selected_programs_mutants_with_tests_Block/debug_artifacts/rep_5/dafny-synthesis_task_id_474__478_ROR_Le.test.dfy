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
var r0 := ReplaceChars("\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"| ==> ("\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceChars("aaaa\U{0002}a", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0002}a"|;
expect forall i :: 0 <= i < |"aaaa\U{0002}a"| ==> ("aaaa\U{0002}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0002}a"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0002}a"[i]);
}
method {:test} Test14() {
var r0 := ReplaceChars("\0a\U{0001}\U{0002}a\U{0004}a\0", '\U{0001}', '\0');
expect |r0| == |"\0a\U{0001}\U{0002}a\U{0004}a\0"|;
expect forall i :: 0 <= i < |"\0a\U{0001}\U{0002}a\U{0004}a\0"| ==> ("\0a\U{0001}\U{0002}a\U{0004}a\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\U{0001}\U{0002}a\U{0004}a\0"[i] != '\U{0001}' ==> r0[i] == "\0a\U{0001}\U{0002}a\U{0004}a\0"[i]);
}

// REPEAT 5 - TIME: 10.1766674 s
