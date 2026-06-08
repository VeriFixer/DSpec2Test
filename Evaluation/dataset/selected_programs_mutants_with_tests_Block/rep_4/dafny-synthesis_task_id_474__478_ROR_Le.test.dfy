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

method {:test} Test9() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i]);
}
method {:test} Test10() {
var r0 := ReplaceChars("\U{0004}a\U{0002}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"\U{0004}a\U{0002}\U{0006}"|;
expect forall i :: 0 <= i < |"\U{0004}a\U{0002}\U{0006}"| ==> ("\U{0004}a\U{0002}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0004}a\U{0002}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "\U{0004}a\U{0002}\U{0006}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceChars("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"| ==> ("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i]);
}

// REPEAT 4 - TIME: 8.6296019 s
