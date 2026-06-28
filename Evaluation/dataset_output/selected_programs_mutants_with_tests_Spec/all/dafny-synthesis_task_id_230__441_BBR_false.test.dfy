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
    if false {
      s' := s' + [ch];
    } else {
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

// REPEAT 1 - TIME: 3.2404572 s

method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("a ", '\0');
expect |r0| == |"a "|;
expect forall i :: 0 <= i < |"a "| ==> ("a "[i] == ' ' ==> r0[i] == '\0') && ("a "[i] != ' ' ==> r0[i] == "a "[i]);
}

// REPEAT 2 - TIME: 4.3416019 s

method {:test} Test2() {
var r0 := ReplaceBlanksWithChar("a\0aaaaaaaaaa ", '\0');
expect |r0| == |"a\0aaaaaaaaaa "|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaa "| ==> ("a\0aaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("a\0aaaaaaaaaa "[i] != ' ' ==> r0[i] == "a\0aaaaaaaaaa "[i]);
}

// REPEAT 3 - TIME: 5.228056 s

method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("a\0a", '\0');
expect |r0| == |"a\0a"|;
expect forall i :: 0 <= i < |"a\0a"| ==> ("a\0a"[i] == ' ' ==> r0[i] == '\0') && ("a\0a"[i] != ' ' ==> r0[i] == "a\0a"[i]);
}

// REPEAT 4 - TIME: 6.0399087 s

method {:test} Test4() {
var r0 := ReplaceBlanksWithChar("\0\0", '\0');
expect |r0| == |"\0\0"|;
expect forall i :: 0 <= i < |"\0\0"| ==> ("\0\0"[i] == ' ' ==> r0[i] == '\0') && ("\0\0"[i] != ' ' ==> r0[i] == "\0\0"[i]);
}

// REPEAT 5 - TIME: 7.0373561 s

method {:test} Test5() {
var r0 := ReplaceBlanksWithChar(" aa", '\0');
expect |r0| == |" aa"|;
expect forall i :: 0 <= i < |" aa"| ==> (" aa"[i] == ' ' ==> r0[i] == '\0') && (" aa"[i] != ' ' ==> r0[i] == " aa"[i]);
}

// REPEAT 6 - TIME: 7.9628107 s

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaaa ", '\0');
expect |r0| == |"  aaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"  aaaaaaaaaaa "| ==> ("  aaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaaa "[i] != ' ' ==> r0[i] == "  aaaaaaaaaaa "[i]);
}

// REPEAT 7 - TIME: 8.7008803 s

method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a", '\0');
expect |r0| == |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"|;
expect forall i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"| ==> ("\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"[i] != ' ' ==> r0[i] == "\U{0003}\U{0001}aaaaaaaaaaa\U{0005}a"[i]);
}

// REPEAT 8 - TIME: 9.4459709 s

method {:test} Test8() {
var r0 := ReplaceBlanksWithChar("\0a\0\0", '\0');
expect |r0| == |"\0a\0\0"|;
expect forall i :: 0 <= i < |"\0a\0\0"| ==> ("\0a\0\0"[i] == ' ' ==> r0[i] == '\0') && ("\0a\0\0"[i] != ' ' ==> r0[i] == "\0a\0\0"[i]);
}

// REPEAT 9 - TIME: 10.2497455 s

method {:test} Test9() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaa\U{0003}a\U{0007}aaaaaa\U{0005}a", '\0');
expect |r0| == |"\U{0001}aaa\U{0003}a\U{0007}aaaaaa\U{0005}a"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0003}a\U{0007}aaaaaa\U{0005}a"| ==> ("\U{0001}aaa\U{0003}a\U{0007}aaaaaa\U{0005}a"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0003}a\U{0007}aaaaaa\U{0005}a"[i] != ' ' ==> r0[i] == "\U{0001}aaa\U{0003}a\U{0007}aaaaaa\U{0005}a"[i]);
}

// REPEAT 10 - TIME: 11.122702 s
