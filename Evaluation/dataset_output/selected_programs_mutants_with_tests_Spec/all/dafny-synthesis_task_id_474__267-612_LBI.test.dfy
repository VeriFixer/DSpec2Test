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
    break;
    if s[i] == oldChar {
      s' := s' + [newChar];
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

// REPEAT 1 - TIME: 2.7488928 s

method {:test} Test1() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\0"| ==> ("aaaaaaaaaaaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\0"[i]);
}

// REPEAT 2 - TIME: 3.7122951 s

method {:test} Test2() {
var r0 := ReplaceChars("aaaa\0aaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaa\0aaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaa\0aaaaaaaaaaaaaaaa\U{0001}"| ==> ("aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaa\0aaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 4.6724511 s

method {:test} Test3() {
var r0 := ReplaceChars("\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}"| ==> ("\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}"[i]);
}

// REPEAT 4 - TIME: 5.6230757 s

method {:test} Test4() {
var r0 := ReplaceChars("\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}"| ==> ("\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}"[i]);
}

// REPEAT 5 - TIME: 6.6790623 s

method {:test} Test5() {
var r0 := ReplaceChars("\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aa"| ==> ("\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa"[i]);
}

// REPEAT 6 - TIME: 7.6844921 s

method {:test} Test6() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 7 - TIME: 8.6516207 s

method {:test} Test7() {
var r0 := ReplaceChars("\U{0001}\U{0001}\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}\U{0001}a"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}\U{0001}a"| ==> ("\U{0001}\U{0001}\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}\U{0001}a"[i]);
}

// REPEAT 8 - TIME: 9.4400233 s

method {:test} Test8() {
var r0 := ReplaceChars("\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}"| ==> ("\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}"[i]);
}

// REPEAT 9 - TIME: 10.2853867 s

method {:test} Test9() {
var r0 := ReplaceChars("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"| ==> ("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}\U{0001}"[i]);
}

// REPEAT 10 - TIME: 10.8738368 s
