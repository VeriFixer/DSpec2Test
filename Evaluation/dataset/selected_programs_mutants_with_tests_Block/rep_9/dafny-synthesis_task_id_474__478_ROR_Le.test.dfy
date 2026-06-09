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
var r0 := ReplaceChars("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"| ==> ("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i]);
}
method {:test} Test25() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i]);
}
method {:test} Test26() {
var r0 := ReplaceChars("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"| ==> ("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i]);
}

// REPEAT 9 - TIME: 15.4766826 s
