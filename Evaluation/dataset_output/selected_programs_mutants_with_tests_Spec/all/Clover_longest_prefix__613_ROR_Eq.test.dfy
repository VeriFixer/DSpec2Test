// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if |str1| < |str2| then |str1| else |str2|;
  for idx := 0 to minLength
    invariant |prefix| == idx <= minLength <= |str1| && minLength <= |str2|
    invariant |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  {
    if str1[idx] == str2[idx] {
      return;
    }
    prefix := prefix + [str1[idx]];
  }
}


method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{
  prefix := [];
  var minLength := if |str1| <|str2| then |str1| else |str2|;

  for idx:= 0 to minLength
    invariant |prefix|==idx <=  minLength<=|str1| && minLength<=|str2|
    invariant |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  {
    if str1[idx] != str2[idx] {
      return;
    }
    prefix := prefix + [str1[idx]];
  }
}

method {:test} Test0() {
var r0 := LongestCommonPrefix("a", "a");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |"a"| || "a"[|r0|] != "a"[|r0|];
}
method {:test} Test1() {
var r0 := LongestCommonPrefix("aa", "a");
expect |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"aa"| || |r0| == |"a"| || "aa"[|r0|] != "a"[|r0|];
}
method {:test} Test2() {
var r0 := LongestCommonPrefix("a\0", "a\U{0002}");
expect |r0| <= |"a\0"| && r0 == "a\0"[0 .. |r0|] && |r0| <= |"a\U{0002}"| && r0 == "a\U{0002}"[0 .. |r0|];
expect |r0| == |"a\0"| || |r0| == |"a\U{0002}"| || "a\0"[|r0|] != "a\U{0002}"[|r0|];
}

// REPEAT 1 - TIME: 2.8964643 s

method {:test} Test3() {
var r0 := LongestCommonPrefix("aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa", "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0");
expect |r0| <= |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"| && r0 == "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"| || "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaa", "\U{0002}\0aaaaaaaaa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaa"| || |r0| == |"\U{0002}\0aaaaaaaaa"| || "\U{0002}\0aaaaaaaaaa"[|r0|] != "\U{0002}\0aaaaaaaaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0006}\U{0004}", "\U{0006}\0\U{0002}\U{0008}");
expect |r0| <= |"\U{0006}\U{0004}"| && r0 == "\U{0006}\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0006}\0\U{0002}\U{0008}"| && r0 == "\U{0006}\0\U{0002}\U{0008}"[0 .. |r0|];
expect |r0| == |"\U{0006}\U{0004}"| || |r0| == |"\U{0006}\0\U{0002}\U{0008}"| || "\U{0006}\U{0004}"[|r0|] != "\U{0006}\0\U{0002}\U{0008}"[|r0|];
}

// REPEAT 2 - TIME: 4.1116195 s

method {:test} Test6() {
var r0 := LongestCommonPrefix("\U{0008}\U{0002}aaaaaaaaaa\U{0006}", "\U{0008}\U{0002}aaaaaaaaaa\U{0006}aaaa\0\U{0004}");
expect |r0| <= |"\U{0008}\U{0002}aaaaaaaaaa\U{0006}"| && r0 == "\U{0008}\U{0002}aaaaaaaaaa\U{0006}"[0 .. |r0|] && |r0| <= |"\U{0008}\U{0002}aaaaaaaaaa\U{0006}aaaa\0\U{0004}"| && r0 == "\U{0008}\U{0002}aaaaaaaaaa\U{0006}aaaa\0\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0008}\U{0002}aaaaaaaaaa\U{0006}"| || |r0| == |"\U{0008}\U{0002}aaaaaaaaaa\U{0006}aaaa\0\U{0004}"| || "\U{0008}\U{0002}aaaaaaaaaa\U{0006}"[|r0|] != "\U{0008}\U{0002}aaaaaaaaaa\U{0006}aaaa\0\U{0004}"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("a\0aaaaa\U{0004}\U{0002}", "a\0aaaaa\U{0004}");
expect |r0| <= |"a\0aaaaa\U{0004}\U{0002}"| && r0 == "a\0aaaaa\U{0004}\U{0002}"[0 .. |r0|] && |r0| <= |"a\0aaaaa\U{0004}"| && r0 == "a\0aaaaa\U{0004}"[0 .. |r0|];
expect |r0| == |"a\0aaaaa\U{0004}\U{0002}"| || |r0| == |"a\0aaaaa\U{0004}"| || "a\0aaaaa\U{0004}\U{0002}"[|r0|] != "a\0aaaaa\U{0004}"[|r0|];
}
method {:test} Test8() {
var r0 := LongestCommonPrefix("\U{0004}\U{0006}\U{0002}", "\U{0004}\U{0008}\0");
expect |r0| <= |"\U{0004}\U{0006}\U{0002}"| && r0 == "\U{0004}\U{0006}\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0008}\0"| && r0 == "\U{0004}\U{0008}\0"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0006}\U{0002}"| || |r0| == |"\U{0004}\U{0008}\0"| || "\U{0004}\U{0006}\U{0002}"[|r0|] != "\U{0004}\U{0008}\0"[|r0|];
}

// REPEAT 3 - TIME: 5.3260122 s

method {:test} Test9() {
var r0 := LongestCommonPrefix("\U{0006}aa\U{0002}", "\U{0006}aa\U{0002}\U{0004}a\0");
expect |r0| <= |"\U{0006}aa\U{0002}"| && r0 == "\U{0006}aa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0006}aa\U{0002}\U{0004}a\0"| && r0 == "\U{0006}aa\U{0002}\U{0004}a\0"[0 .. |r0|];
expect |r0| == |"\U{0006}aa\U{0002}"| || |r0| == |"\U{0006}aa\U{0002}\U{0004}a\0"| || "\U{0006}aa\U{0002}"[|r0|] != "\U{0006}aa\U{0002}\U{0004}a\0"[|r0|];
}
method {:test} Test10() {
var r0 := LongestCommonPrefix("\U{0008}\0aaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}aaaaaa", "\U{0008}\0aaaaaaa\U{0002}a\U{0006}");
expect |r0| <= |"\U{0008}\0aaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}aaaaaa"| && r0 == "\U{0008}\0aaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}aaaaaa"[0 .. |r0|] && |r0| <= |"\U{0008}\0aaaaaaa\U{0002}a\U{0006}"| && r0 == "\U{0008}\0aaaaaaa\U{0002}a\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}aaaaaa"| || |r0| == |"\U{0008}\0aaaaaaa\U{0002}a\U{0006}"| || "\U{0008}\0aaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}aaaaaa"[|r0|] != "\U{0008}\0aaaaaaa\U{0002}a\U{0006}"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\0\U{0002}aa", "\0\U{0004}aaa");
expect |r0| <= |"\0\U{0002}aa"| && r0 == "\0\U{0002}aa"[0 .. |r0|] && |r0| <= |"\0\U{0004}aaa"| && r0 == "\0\U{0004}aaa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aa"| || |r0| == |"\0\U{0004}aaa"| || "\0\U{0002}aa"[|r0|] != "\0\U{0004}aaa"[|r0|];
}

// REPEAT 4 - TIME: 6.5784105 s

method {:test} Test12() {
var r0 := LongestCommonPrefix("\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}", "\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}");
expect |r0| <= |"\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"| && r0 == "\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"[0 .. |r0|] && |r0| <= |"\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"| && r0 == "\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"| || |r0| == |"\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"| || "\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"[|r0|] != "\U{000E}\0aa\n\U{0006}\U{0008}\U{0004}\U{000C}\U{0002}"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\U{000C}\0a\U{0002}a\na\U{0008}\U{0006}\U{0004}aa", "\U{000C}\0a\U{0002}a\n");
expect |r0| <= |"\U{000C}\0a\U{0002}a\na\U{0008}\U{0006}\U{0004}aa"| && r0 == "\U{000C}\0a\U{0002}a\na\U{0008}\U{0006}\U{0004}aa"[0 .. |r0|] && |r0| <= |"\U{000C}\0a\U{0002}a\n"| && r0 == "\U{000C}\0a\U{0002}a\n"[0 .. |r0|];
expect |r0| == |"\U{000C}\0a\U{0002}a\na\U{0008}\U{0006}\U{0004}aa"| || |r0| == |"\U{000C}\0a\U{0002}a\n"| || "\U{000C}\0a\U{0002}a\na\U{0008}\U{0006}\U{0004}aa"[|r0|] != "\U{000C}\0a\U{0002}a\n"[|r0|];
}
method {:test} Test14() {
var r0 := LongestCommonPrefix("\U{0004}\U{0002}a", "\U{0004}\0aa");
expect |r0| <= |"\U{0004}\U{0002}a"| && r0 == "\U{0004}\U{0002}a"[0 .. |r0|] && |r0| <= |"\U{0004}\0aa"| && r0 == "\U{0004}\0aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0002}a"| || |r0| == |"\U{0004}\0aa"| || "\U{0004}\U{0002}a"[|r0|] != "\U{0004}\0aa"[|r0|];
}

// REPEAT 5 - TIME: 7.5912031 s

method {:test} Test15() {
var r0 := LongestCommonPrefix("\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a", "\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a\0");
expect |r0| <= |"\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a"| && r0 == "\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a"[0 .. |r0|] && |r0| <= |"\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a\0"| && r0 == "\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a\0"[0 .. |r0|];
expect |r0| == |"\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a"| || |r0| == |"\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a\0"| || "\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a"[|r0|] != "\U{0008}aaaaaaaa\U{0004}aa\U{0006}a\U{0002}a\0"[|r0|];
}
method {:test} Test16() {
var r0 := LongestCommonPrefix("\U{0008}aaaa\0\U{0006}\U{0004}\U{0002}aa", "\U{0008}aaaa");
expect |r0| <= |"\U{0008}aaaa\0\U{0006}\U{0004}\U{0002}aa"| && r0 == "\U{0008}aaaa\0\U{0006}\U{0004}\U{0002}aa"[0 .. |r0|] && |r0| <= |"\U{0008}aaaa"| && r0 == "\U{0008}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0008}aaaa\0\U{0006}\U{0004}\U{0002}aa"| || |r0| == |"\U{0008}aaaa"| || "\U{0008}aaaa\0\U{0006}\U{0004}\U{0002}aa"[|r0|] != "\U{0008}aaaa"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaa", "\U{0004}\U{0002}aaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaa"| && r0 == "\U{0004}\U{0002}aaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaa"| || "\U{0004}\0aaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaa"[|r0|];
}

// REPEAT 6 - TIME: 8.4639391 s

method {:test} Test18() {
var r0 := LongestCommonPrefix("a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}", "a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}");
expect |r0| <= |"a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"| && r0 == "a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"[0 .. |r0|] && |r0| <= |"a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"| && r0 == "a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"[0 .. |r0|];
expect |r0| == |"a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"| || |r0| == |"a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"| || "a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"[|r0|] != "a\0a\U{0004}\U{0006}aaaa\U{000C}aaa\U{000E}\n\U{0002}aaa\U{0010}aaa\U{0008}aaaa\U{0012}\U{0014}"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}aaaaa\U{0006}a\naa", "aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}");
expect |r0| <= |"aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}aaaaa\U{0006}a\naa"| && r0 == "aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}aaaaa\U{0006}a\naa"[0 .. |r0|] && |r0| <= |"aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}"| && r0 == "aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}"[0 .. |r0|];
expect |r0| == |"aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}aaaaa\U{0006}a\naa"| || |r0| == |"aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}"| || "aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}aaaaa\U{0006}a\naa"[|r0|] != "aaaaaa\0\U{0004}aaaaa\U{0002}a\U{0008}\U{000C}aa\U{000E}"[|r0|];
}
method {:test} Test20() {
var r0 := LongestCommonPrefix("\U{0014}\U{0016}aa\0aaaa\naaa\U{000E}\U{0002}aaaaaaaaaaaaa\U{0012}a", "\U{0014}\U{0018}aaa\U{0004}a\U{0006}aaa\U{000C}aaaaa\U{0008}a\U{0010}");
expect |r0| <= |"\U{0014}\U{0016}aa\0aaaa\naaa\U{000E}\U{0002}aaaaaaaaaaaaa\U{0012}a"| && r0 == "\U{0014}\U{0016}aa\0aaaa\naaa\U{000E}\U{0002}aaaaaaaaaaaaa\U{0012}a"[0 .. |r0|] && |r0| <= |"\U{0014}\U{0018}aaa\U{0004}a\U{0006}aaa\U{000C}aaaaa\U{0008}a\U{0010}"| && r0 == "\U{0014}\U{0018}aaa\U{0004}a\U{0006}aaa\U{000C}aaaaa\U{0008}a\U{0010}"[0 .. |r0|];
expect |r0| == |"\U{0014}\U{0016}aa\0aaaa\naaa\U{000E}\U{0002}aaaaaaaaaaaaa\U{0012}a"| || |r0| == |"\U{0014}\U{0018}aaa\U{0004}a\U{0006}aaa\U{000C}aaaaa\U{0008}a\U{0010}"| || "\U{0014}\U{0016}aa\0aaaa\naaa\U{000E}\U{0002}aaaaaaaaaaaaa\U{0012}a"[|r0|] != "\U{0014}\U{0018}aaa\U{0004}a\U{0006}aaa\U{000C}aaaaa\U{0008}a\U{0010}"[|r0|];
}

// REPEAT 7 - TIME: 9.2491309 s

method {:test} Test21() {
var r0 := LongestCommonPrefix("\naaa\0", "\naaa\0aa\U{0004}a\U{0002}aaa\U{0008}aa\U{0006}aaaa");
expect |r0| <= |"\naaa\0"| && r0 == "\naaa\0"[0 .. |r0|] && |r0| <= |"\naaa\0aa\U{0004}a\U{0002}aaa\U{0008}aa\U{0006}aaaa"| && r0 == "\naaa\0aa\U{0004}a\U{0002}aaa\U{0008}aa\U{0006}aaaa"[0 .. |r0|];
expect |r0| == |"\naaa\0"| || |r0| == |"\naaa\0aa\U{0004}a\U{0002}aaa\U{0008}aa\U{0006}aaaa"| || "\naaa\0"[|r0|] != "\naaa\0aa\U{0004}a\U{0002}aaa\U{0008}aa\U{0006}aaaa"[|r0|];
}
method {:test} Test22() {
var r0 := LongestCommonPrefix("\U{0006}aaaaaaaaaa\0aaa\U{0002}aaaaa\U{0004}aaaaa", "\U{0006}aaaaaaaa");
expect |r0| <= |"\U{0006}aaaaaaaaaa\0aaa\U{0002}aaaaa\U{0004}aaaaa"| && r0 == "\U{0006}aaaaaaaaaa\0aaa\U{0002}aaaaa\U{0004}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0006}aaaaaaaa"| && r0 == "\U{0006}aaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0006}aaaaaaaaaa\0aaa\U{0002}aaaaa\U{0004}aaaaa"| || |r0| == |"\U{0006}aaaaaaaa"| || "\U{0006}aaaaaaaaaa\0aaa\U{0002}aaaaa\U{0004}aaaaa"[|r0|] != "\U{0006}aaaaaaaa"[|r0|];
}
method {:test} Test23() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaa", "\U{0004}\U{0002}aa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aa"| && r0 == "\U{0004}\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aa"| || "\U{0004}\0aaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aa"[|r0|];
}

// REPEAT 8 - TIME: 10.1111678 s

method {:test} Test24() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test25() {
var r0 := LongestCommonPrefix("\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa\U{0006}a", "\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa");
expect |r0| <= |"\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa\U{0006}a"| && r0 == "\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa\U{0006}a"[0 .. |r0|] && |r0| <= |"\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa"| && r0 == "\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa"[0 .. |r0|];
expect |r0| == |"\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa\U{0006}a"| || |r0| == |"\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa"| || "\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa\U{0006}a"[|r0|] != "\U{000C}aaaa\U{0002}a\U{0004}aaaaaaa\U{0008}aaa\naaa\0aa"[|r0|];
}
method {:test} Test26() {
var r0 := LongestCommonPrefix("\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaa\0aaaaa", "\U{0004}\U{0008}aaaaaaaaaaaa\U{0002}aaa");
expect |r0| <= |"\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaa\0aaaaa"| && r0 == "\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaa\0aaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0008}aaaaaaaaaaaa\U{0002}aaa"| && r0 == "\U{0004}\U{0008}aaaaaaaaaaaa\U{0002}aaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaa\0aaaaa"| || |r0| == |"\U{0004}\U{0008}aaaaaaaaaaaa\U{0002}aaa"| || "\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaa\0aaaaa"[|r0|] != "\U{0004}\U{0008}aaaaaaaaaaaa\U{0002}aaa"[|r0|];
}

// REPEAT 9 - TIME: 11.0646358 s

method {:test} Test27() {
var r0 := LongestCommonPrefix("aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa", "aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa\U{0004}\U{0008}");
expect |r0| <= |"aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa"| && r0 == "aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa\U{0004}\U{0008}"| && r0 == "aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa\U{0004}\U{0008}"[0 .. |r0|];
expect |r0| == |"aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa"| || |r0| == |"aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa\U{0004}\U{0008}"| || "aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa"[|r0|] != "aaaaa\U{0002}aaa\U{0006}\0aaaaaaaaaaaaaaa\U{0004}\U{0008}"[|r0|];
}
method {:test} Test28() {
var r0 := LongestCommonPrefix("\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}aaa\0", "\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}a");
expect |r0| <= |"\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}aaa\0"| && r0 == "\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}aaa\0"[0 .. |r0|] && |r0| <= |"\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}a"| && r0 == "\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}a"[0 .. |r0|];
expect |r0| == |"\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}aaa\0"| || |r0| == |"\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}a"| || "\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}aaa\0"[|r0|] != "\U{0008}aaaaaaaa\U{0002}aaaaaaaaa\U{0004}a\U{0006}a"[|r0|];
}
method {:test} Test29() {
var r0 := LongestCommonPrefix("a\U{0006}aaaaaaaaaaaa\0aaaaaaaaaaa", "a\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}a");
expect |r0| <= |"a\U{0006}aaaaaaaaaaaa\0aaaaaaaaaaa"| && r0 == "a\U{0006}aaaaaaaaaaaa\0aaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}a"| && r0 == "a\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}a"[0 .. |r0|];
expect |r0| == |"a\U{0006}aaaaaaaaaaaa\0aaaaaaaaaaa"| || |r0| == |"a\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}a"| || "a\U{0006}aaaaaaaaaaaa\0aaaaaaaaaaa"[|r0|] != "a\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}a"[|r0|];
}

// REPEAT 10 - TIME: 11.9529972 s
