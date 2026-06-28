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
var r0 := ReplaceChars("aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceChars("aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"| ==> ("aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"| ==> ("\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 18.426497 s
