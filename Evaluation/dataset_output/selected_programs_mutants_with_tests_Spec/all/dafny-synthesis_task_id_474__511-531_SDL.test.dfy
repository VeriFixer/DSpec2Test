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

// REPEAT 1 - TIME: 3.0817264 s

method {:test} Test1() {
var r0 := ReplaceChars("aaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaa\0"| ==> ("aaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaa\0"[i]);
}

// REPEAT 2 - TIME: 4.0802137 s

method {:test} Test2() {
var r0 := ReplaceChars("aa\U{0002}", '\U{0001}', '\0');
expect |r0| == |"aa\U{0002}"|;
expect forall i :: 0 <= i < |"aa\U{0002}"| ==> ("aa\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\U{0002}"[i] != '\U{0001}' ==> r0[i] == "aa\U{0002}"[i]);
}

// REPEAT 3 - TIME: 5.1456977 s

method {:test} Test3() {
var r0 := ReplaceChars("\U{0002}\0", '\U{0001}', '\0');
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> ("\U{0002}\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}\0"[i] != '\U{0001}' ==> r0[i] == "\U{0002}\0"[i]);
}

// REPEAT 4 - TIME: 6.2015164 s

method {:test} Test4() {
var r0 := ReplaceChars("\0aaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\0aaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaa"| ==> ("\0aaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\0aaaaaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 7.1212383 s

method {:test} Test5() {
var r0 := ReplaceChars("\U{0001}aa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa\U{0001}a"|;
expect forall i :: 0 <= i < |"\U{0001}aa\U{0001}a"| ==> ("\U{0001}aa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa\U{0001}a"[i]);
}

// REPEAT 6 - TIME: 8.1997669 s

method {:test} Test6() {
var r0 := ReplaceChars("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"|;
expect forall i :: 0 <= i < |"aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"| ==> ("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i]);
}

// REPEAT 7 - TIME: 8.9251334 s

method {:test} Test7() {
var r0 := ReplaceChars("\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}"| ==> ("\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}"[i]);
}

// REPEAT 8 - TIME: 9.5614293 s

method {:test} Test8() {
var r0 := ReplaceChars("\U{0001}\U{0001}aaa\U{0001}aaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}aaa\U{0001}aaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}aaa\U{0001}aaaaaaa\U{0001}"| ==> ("\U{0001}\U{0001}aaa\U{0001}aaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}aaa\U{0001}aaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}aaa\U{0001}aaaaaaa\U{0001}"[i]);
}

// REPEAT 9 - TIME: 10.3957617 s

method {:test} Test9() {
var r0 := ReplaceChars("\U{0001}aaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaa"| ==> ("\U{0001}aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa"[i]);
}

// REPEAT 10 - TIME: 11.2525419 s
