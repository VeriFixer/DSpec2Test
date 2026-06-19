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
method {:test} Test1() {
var r0 := ReplaceChars("", '\U{0001}', '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == '\U{0001}' ==> r0[i] == '\0') && (""[i] != '\U{0001}' ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceChars("aa", '\U{0001}', '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa"[i] != '\U{0001}' ==> r0[i] == "aa"[i]);
}

// REPEAT 1 - TIME: 7.039998 s

method {:test} Test10() {
var r0 := ReplaceChars("aa\U{0003}aaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aa\U{0003}aaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aa\U{0003}aaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("aa\U{0003}aaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\U{0003}aaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aa\U{0003}aaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 8.1447494 s

method {:test} Test11() {
var r0 := ReplaceChars("\0a\0", '\U{0001}', '\0');
expect |r0| == |"\0a\0"|;
expect forall i :: 0 <= i < |"\0a\0"| ==> ("\0a\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\0"[i] != '\U{0001}' ==> r0[i] == "\0a\0"[i]);
}

// REPEAT 3 - TIME: 9.0812192 s

method {:test} Test12() {
var r0 := ReplaceChars("a\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"a\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"a\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}"| ==> ("a\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "a\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 4 - TIME: 9.8720735 s

method {:test} Test13() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaa\U{0001}"| ==> ("\U{0001}aaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 5 - TIME: 10.6899524 s

method {:test} Test14() {
var r0 := ReplaceChars("\U{0001}aaaaa\U{0001}aaaaaaaa\U{0001}aaaa\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaa\U{0001}aaaaaaaa\U{0001}aaaa\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaa\U{0001}aaaaaaaa\U{0001}aaaa\U{0001}a\U{0001}"| ==> ("\U{0001}aaaaa\U{0001}aaaaaaaa\U{0001}aaaa\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaa\U{0001}aaaaaaaa\U{0001}aaaa\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaa\U{0001}aaaaaaaa\U{0001}aaaa\U{0001}a\U{0001}"[i]);
}

// REPEAT 6 - TIME: 11.4688823 s

method {:test} Test15() {
var r0 := ReplaceChars("\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}"| ==> ("\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}"[i]);
}

// REPEAT 7 - TIME: 12.2665495 s

method {:test} Test16() {
var r0 := ReplaceChars("\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}"| ==> ("\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}"[i]);
}

// REPEAT 8 - TIME: 12.9744611 s

method {:test} Test17() {
var r0 := ReplaceChars("\U{0001}\U{0001}aaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}aaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}aaaaaaaaaaaaaaaaaaa"| ==> ("\U{0001}\U{0001}aaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}aaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}aaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 9 - TIME: 13.6256135 s

method {:test} Test18() {
var r0 := ReplaceChars("\U{0001}aa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aa\U{0001}"| ==> ("\U{0001}aa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa\U{0001}"[i]);
}

// REPEAT 10 - TIME: 14.424579 s
