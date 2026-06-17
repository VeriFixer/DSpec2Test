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


method {:testEntry} ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == oldChar ==> s'[k] == newChar) && (s[k] != oldChar ==> s'[k] == s[k])
    {
        if s[i] == oldChar
        {
            s' := s' + [newChar];
        }
        else 
        {
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

// REPEAT 1 - TIME: 7.0543929 s

method {:test} Test10() {
var r0 := ReplaceChars("aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 7.9731791 s

method {:test} Test11() {
var r0 := ReplaceChars("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"|;
expect forall i :: 0 <= i < |"aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"| ==> ("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i]);
}

// REPEAT 3 - TIME: 8.7039327 s

method {:test} Test12() {
var r0 := ReplaceChars("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 4 - TIME: 9.4357457 s

method {:test} Test13() {
var r0 := ReplaceChars("\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aa"| ==> ("\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa"[i]);
}

// REPEAT 5 - TIME: 10.1365943 s

method {:test} Test14() {
var r0 := ReplaceChars("\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 6 - TIME: 10.7849175 s

method {:test} Test15() {
var r0 := ReplaceChars("\U{0001}a\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}\U{0001}"| ==> ("\U{0001}a\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}\U{0001}"[i]);
}

// REPEAT 7 - TIME: 11.572111 s

method {:test} Test16() {
var r0 := ReplaceChars("\U{0001}aaa\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}\U{0001}\U{0001}"| ==> ("\U{0001}aaa\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}\U{0001}\U{0001}"[i]);
}

// REPEAT 8 - TIME: 12.408462 s

method {:test} Test17() {
var r0 := ReplaceChars("aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"| ==> ("aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"[i]);
}

// REPEAT 9 - TIME: 13.2448086 s

method {:test} Test18() {
var r0 := ReplaceChars("aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"| ==> ("aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"[i]);
}

// REPEAT 10 - TIME: 14.1257903 s
