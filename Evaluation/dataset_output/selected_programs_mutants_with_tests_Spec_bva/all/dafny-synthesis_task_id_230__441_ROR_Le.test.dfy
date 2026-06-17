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
    if s[i] <= ' ' {
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
method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa", '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == ' ' ==> r0[i] == '\0') && ("aa"[i] != ' ' ==> r0[i] == "aa"[i]);
}

// REPEAT 1 - TIME: 6.9018899 s

method {:test} Test10() {
var r0 := ReplaceBlanksWithChar(" \0", '\0');
expect |r0| == |" \0"|;
expect forall i :: 0 <= i < |" \0"| ==> (" \0"[i] == ' ' ==> r0[i] == '\0') && (" \0"[i] != ' ' ==> r0[i] == " \0"[i]);
}

// REPEAT 2 - TIME: 8.1413537 s

method {:test} Test11() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaa\U{0003}", '\0');
expect |r0| == |"  aaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"  aaaaaaaaa\U{0003}"| ==> ("  aaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "  aaaaaaaaa\U{0003}"[i]);
}

// REPEAT 3 - TIME: 8.8648584 s

method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("aaa", '\0');
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> ("aaa"[i] == ' ' ==> r0[i] == '\0') && ("aaa"[i] != ' ' ==> r0[i] == "aaa"[i]);
}

// REPEAT 4 - TIME: 9.5879384 s

method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ", '\0');
expect |r0| == |"a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "| ==> ("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i] != ' ' ==> r0[i] == "a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 5 - TIME: 10.2026389 s

method {:test} Test14() {
var r0 := ReplaceBlanksWithChar("\0\0aaaaaaaaaa\0", '\0');
expect |r0| == |"\0\0aaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\0\0aaaaaaaaaa\0"| ==> ("\0\0aaaaaaaaaa\0"[i] == ' ' ==> r0[i] == '\0') && ("\0\0aaaaaaaaaa\0"[i] != ' ' ==> r0[i] == "\0\0aaaaaaaaaa\0"[i]);
}

// REPEAT 6 - TIME: 11.0004365 s

method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("\U{0003}\U{0001} a a aaaaaaaa", '\0');
expect |r0| == |"\U{0003}\U{0001} a a aaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0003}\U{0001} a a aaaaaaaa"| ==> ("\U{0003}\U{0001} a a aaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}\U{0001} a a aaaaaaaa"[i] != ' ' ==> r0[i] == "\U{0003}\U{0001} a a aaaaaaaa"[i]);
}

// REPEAT 7 - TIME: 11.6987443 s

method {:test} Test16() {
var r0 := ReplaceBlanksWithChar(" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a ", '\0');
expect |r0| == |" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "|;
expect forall i :: 0 <= i < |" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "| ==> (" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i] == ' ' ==> r0[i] == '\0') && (" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i] != ' ' ==> r0[i] == " a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]);
}

// REPEAT 8 - TIME: 12.2656082 s

method {:test} Test17() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaa  a ", '\0');
expect |r0| == |"  aaaaaaaaaa  a "|;
expect forall i :: 0 <= i < |"  aaaaaaaaaa  a "| ==> ("  aaaaaaaaaa  a "[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaa  a "[i] != ' ' ==> r0[i] == "  aaaaaaaaaa  a "[i]);
}

// REPEAT 9 - TIME: 13.0055917 s

method {:test} Test18() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaa  a  a  ", '\0');
expect |r0| == |" aaaaaaaa  a  a  "|;
expect forall i :: 0 <= i < |" aaaaaaaa  a  a  "| ==> (" aaaaaaaa  a  a  "[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaa  a  a  "[i] != ' ' ==> r0[i] == " aaaaaaaa  a  a  "[i]);
}

// REPEAT 10 - TIME: 13.6505136 s
