// dafny-synthesis_task_id_230.dfy

method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
  {
    break;
    if s[i] == ' ' {
      s' := s' + [ch];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
    {
        if s[i] == ' '
        {
            s' := s' + [ch];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test0() {
var r0 := ReplaceBlanksWithChar("a", '\0');
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> ("a"[i] == ' ' ==> r0[i] == '\0') && ("a"[i] != ' ' ==> r0[i] == "a"[i]);
}

// REPEAT 1 - TIME: 2.870477 s

method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("a ", '\0');
expect |r0| == |"a "|;
expect forall i :: 0 <= i < |"a "| ==> ("a "[i] == ' ' ==> r0[i] == '\0') && ("a "[i] != ' ' ==> r0[i] == "a "[i]);
}

// REPEAT 2 - TIME: 3.8166351 s

method {:test} Test2() {
var r0 := ReplaceBlanksWithChar("  ", '\0');
expect |r0| == |"  "|;
expect forall i :: 0 <= i < |"  "| ==> ("  "[i] == ' ' ==> r0[i] == '\0') && ("  "[i] != ' ' ==> r0[i] == "  "[i]);
}

// REPEAT 3 - TIME: 4.8178665 s

method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("\0 ", '\0');
expect |r0| == |"\0 "|;
expect forall i :: 0 <= i < |"\0 "| ==> ("\0 "[i] == ' ' ==> r0[i] == '\0') && ("\0 "[i] != ' ' ==> r0[i] == "\0 "[i]);
}

// REPEAT 4 - TIME: 5.817304 s

method {:test} Test4() {
var r0 := ReplaceBlanksWithChar("\0\U{0001}a", '\0');
expect |r0| == |"\0\U{0001}a"|;
expect forall i :: 0 <= i < |"\0\U{0001}a"| ==> ("\0\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("\0\U{0001}a"[i] != ' ' ==> r0[i] == "\0\U{0001}a"[i]);
}

// REPEAT 5 - TIME: 6.715311 s

method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |"a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"| ==> ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 6 - TIME: 7.4267493 s

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("\U{0003}aaaaaaaaaaaaaa\U{0001}", '\0');
expect |r0| == |"\U{0003}aaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0003}aaaaaaaaaaaaaa\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}aaaaaaaaaaaaaa\U{0001}"[i] != ' ' ==> r0[i] == "\U{0003}aaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 7 - TIME: 8.2538436 s

method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("   a", '\0');
expect |r0| == |"   a"|;
expect forall i :: 0 <= i < |"   a"| ==> ("   a"[i] == ' ' ==> r0[i] == '\0') && ("   a"[i] != ' ' ==> r0[i] == "   a"[i]);
}

// REPEAT 8 - TIME: 8.9981344 s

method {:test} Test8() {
var r0 := ReplaceBlanksWithChar("\0\0a\0\0", '\0');
expect |r0| == |"\0\0a\0\0"|;
expect forall i :: 0 <= i < |"\0\0a\0\0"| ==> ("\0\0a\0\0"[i] == ' ' ==> r0[i] == '\0') && ("\0\0a\0\0"[i] != ' ' ==> r0[i] == "\0\0a\0\0"[i]);
}

// REPEAT 9 - TIME: 9.708349 s

method {:test} Test9() {
var r0 := ReplaceBlanksWithChar("  aa ", '\0');
expect |r0| == |"  aa "|;
expect forall i :: 0 <= i < |"  aa "| ==> ("  aa "[i] == ' ' ==> r0[i] == '\0') && ("  aa "[i] != ' ' ==> r0[i] == "  aa "[i]);
}

// REPEAT 10 - TIME: 10.4269769 s
