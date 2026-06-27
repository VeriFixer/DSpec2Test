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
    if s[i] >= oldChar {
      s' := s' + [newChar];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ReplaceChars("a", '\U{0001}', '\0');
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> ("a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a"[i] != '\U{0001}' ==> r0[i] == "a"[i]);
}

// REPEAT 1 - TIME: 3.5769065 s

method {:test} Test1() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\0"| ==> ("aaaaaaaaaaaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\0"[i]);
}

// REPEAT 2 - TIME: 4.8901398 s

method {:test} Test2() {
var r0 := ReplaceChars("aaaa\0aaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaa\0aaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaa\0aaaaaaaaaaaaaaaa\U{0001}"| ==> ("aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 5.817624 s

method {:test} Test3() {
var r0 := ReplaceChars("\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}"| ==> ("\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}"[i]);
}

// REPEAT 4 - TIME: 6.8413603 s

method {:test} Test4() {
var r0 := ReplaceChars("\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}"| ==> ("\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}"[i]);
}

// REPEAT 5 - TIME: 7.7894755 s

method {:test} Test5() {
var r0 := ReplaceChars("\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aa"| ==> ("\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa"[i]);
}

// REPEAT 6 - TIME: 8.7276516 s

method {:test} Test6() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 7 - TIME: 9.4917135 s

method {:test} Test7() {
var r0 := ReplaceChars("\U{0001}\U{0001}\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}\U{0001}a"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}\U{0001}a"| ==> ("\U{0001}\U{0001}\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}\U{0001}a"[i]);
}

// REPEAT 8 - TIME: 10.1608237 s

method {:test} Test8() {
var r0 := ReplaceChars("\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}"| ==> ("\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}"[i]);
}

// REPEAT 9 - TIME: 10.8579445 s

method {:test} Test9() {
var r0 := ReplaceChars("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"| ==> ("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"[i]);
}

// REPEAT 10 - TIME: 11.8251779 s
