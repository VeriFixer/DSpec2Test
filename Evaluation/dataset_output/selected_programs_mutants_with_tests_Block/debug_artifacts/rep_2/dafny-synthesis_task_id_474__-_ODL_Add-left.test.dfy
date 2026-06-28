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
    if s[i] == oldChar {
      s' := [newChar];
    } else {
      s' := [s[i]];
    }
  }
  return s';
}

method {:test} Test3() {
var r0 := ReplaceChars("\0", '\U{0001}', '\0');
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> ("\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0"[i] != '\U{0001}' ==> r0[i] == "\0"[i]);
}
method {:test} Test4() {
var r0 := ReplaceChars("aaaaaa\U{0002}", '\U{0001}', '\0');
expect |r0| == |"aaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"aaaaaa\U{0002}"| ==> ("aaaaaa\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaa\U{0002}"[i] != '\U{0001}' ==> r0[i] == "aaaaaa\U{0002}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceChars("aaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaa\U{0001}"| ==> ("aaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 5.0648229 s
