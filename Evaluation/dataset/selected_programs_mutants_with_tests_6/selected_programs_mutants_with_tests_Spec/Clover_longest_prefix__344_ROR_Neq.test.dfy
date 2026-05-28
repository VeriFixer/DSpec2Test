// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if |str1| != |str2| then |str1| else |str2|;
  for idx := 0 to minLength
    invariant |prefix| == idx <= minLength <= |str1| && minLength <= |str2|
    invariant |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
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
method {:test} Test3() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaa", "\U{0002}\0aaaaaaaaaaa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaa"| || |r0| == |"\U{0002}\0aaaaaaaaaaa"| || "\U{0002}\0aaaaaaaaaaa"[|r0|] != "\U{0002}\0aaaaaaaaaaa"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\U{0004}\0\U{0006}\U{0002}", "\U{0004}\0\U{0006}");
expect |r0| <= |"\U{0004}\0\U{0006}\U{0002}"| && r0 == "\U{0004}\0\U{0006}\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0\U{0006}"| && r0 == "\U{0004}\0\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0004}\0\U{0006}\U{0002}"| || |r0| == |"\U{0004}\0\U{0006}"| || "\U{0004}\0\U{0006}\U{0002}"[|r0|] != "\U{0004}\0\U{0006}"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0004}\0", "\U{0004}\U{0002}");
expect |r0| <= |"\U{0004}\0"| && r0 == "\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}"| && r0 == "\U{0004}\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}\0"| || |r0| == |"\U{0004}\U{0002}"| || "\U{0004}\0"[|r0|] != "\U{0004}\U{0002}"[|r0|];
}
method {:test} Test6() {
var r0 := LongestCommonPrefix("\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa", "\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa\0");
expect |r0| <= |"\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa"| && r0 == "\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa\0"| && r0 == "\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa\0"[0 .. |r0|];
expect |r0| == |"\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa"| || |r0| == |"\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa\0"| || "\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa"[|r0|] != "\U{0004}aa\U{0002}\U{0006}aaaaaaaaaaaa\0"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("a\0aaaaaa\U{0004}aaa\U{0002}\U{0006}", "a\0aaaaaa\U{0004}aaa");
expect |r0| <= |"a\0aaaaaa\U{0004}aaa\U{0002}\U{0006}"| && r0 == "a\0aaaaaa\U{0004}aaa\U{0002}\U{0006}"[0 .. |r0|] && |r0| <= |"a\0aaaaaa\U{0004}aaa"| && r0 == "a\0aaaaaa\U{0004}aaa"[0 .. |r0|];
expect |r0| == |"a\0aaaaaa\U{0004}aaa\U{0002}\U{0006}"| || |r0| == |"a\0aaaaaa\U{0004}aaa"| || "a\0aaaaaa\U{0004}aaa\U{0002}\U{0006}"[|r0|] != "a\0aaaaaa\U{0004}aaa"[|r0|];
}
method {:test} Test8() {
var r0 := LongestCommonPrefix("\U{0004}\U{0006}aaaaa\U{0002}aaaaaa", "\U{0004}\0a");
expect |r0| <= |"\U{0004}\U{0006}aaaaa\U{0002}aaaaaa"| && r0 == "\U{0004}\U{0006}aaaaa\U{0002}aaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0a"| && r0 == "\U{0004}\0a"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0006}aaaaa\U{0002}aaaaaa"| || |r0| == |"\U{0004}\0a"| || "\U{0004}\U{0006}aaaaa\U{0002}aaaaaa"[|r0|] != "\U{0004}\0a"[|r0|];
}
method {:test} Test9() {
var r0 := LongestCommonPrefix("\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}", "\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}aaaaa\U{0004}aaaaaaaaa\0aaaa\U{0006}");
expect |r0| <= |"\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}"| && r0 == "\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}"[0 .. |r0|] && |r0| <= |"\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}aaaaa\U{0004}aaaaaaaaa\0aaaa\U{0006}"| && r0 == "\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}aaaaa\U{0004}aaaaaaaaa\0aaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}"| || |r0| == |"\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}aaaaa\U{0004}aaaaaaaaa\0aaaa\U{0006}"| || "\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}"[|r0|] != "\U{000E}aaa\U{0008}aaa\U{0002}aaaa\n\U{000C}aaaaa\U{0004}aaaaaaaaa\0aaaa\U{0006}"[|r0|];
}
method {:test} Test10() {
var r0 := LongestCommonPrefix("\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\naaa\U{000C}", "\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\n");
expect |r0| <= |"\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\naaa\U{000C}"| && r0 == "\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\naaa\U{000C}"[0 .. |r0|] && |r0| <= |"\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\n"| && r0 == "\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\n"[0 .. |r0|];
expect |r0| == |"\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\naaa\U{000C}"| || |r0| == |"\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\n"| || "\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\naaa\U{000C}"[|r0|] != "\U{0006}\0\U{0002}aaaaa\U{0008}aaa\U{0004}\n"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\U{0006}\0aaa", "\U{0006}\U{0002}\U{0004}");
expect |r0| <= |"\U{0006}\0aaa"| && r0 == "\U{0006}\0aaa"[0 .. |r0|] && |r0| <= |"\U{0006}\U{0002}\U{0004}"| && r0 == "\U{0006}\U{0002}\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0006}\0aaa"| || |r0| == |"\U{0006}\U{0002}\U{0004}"| || "\U{0006}\0aaa"[|r0|] != "\U{0006}\U{0002}\U{0004}"[|r0|];
}
method {:test} Test12() {
var r0 := LongestCommonPrefix("\U{0002}aa\0", "\U{0002}aa\0aaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}aaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aa\0"| && r0 == "\U{0002}aa\0"[0 .. |r0|] && |r0| <= |"\U{0002}aa\0aaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}aaaaaaaaaaaa"| && r0 == "\U{0002}aa\0aaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}aaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aa\0"| || |r0| == |"\U{0002}aa\0aaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}aaaaaaaaaaaa"| || "\U{0002}aa\0"[|r0|] != "\U{0002}aa\0aaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}aaaaaaaaaaaa"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaa", "\0aaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaa"| && r0 == "\0aaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaa"| && r0 == "\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaa"| || |r0| == |"\0aaaaaaaaa"| || "\0aaaaaaaaaa"[|r0|] != "\0aaaaaaaaa"[|r0|];
}
method {:test} Test14() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}a\0", "\U{0002}\U{0006}a\0");
expect |r0| <= |"\U{0002}\U{0004}a\0"| && r0 == "\U{0002}\U{0004}a\0"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}a\0"| && r0 == "\U{0002}\U{0006}a\0"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}a\0"| || |r0| == |"\U{0002}\U{0006}a\0"| || "\U{0002}\U{0004}a\0"[|r0|] != "\U{0002}\U{0006}a\0"[|r0|];
}
method {:test} Test15() {
var r0 := LongestCommonPrefix("\U{0002}aa", "\U{0002}aaaaaaa\0aa");
expect |r0| <= |"\U{0002}aa"| && r0 == "\U{0002}aa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaa\0aa"| && r0 == "\U{0002}aaaaaaa\0aa"[0 .. |r0|];
expect |r0| == |"\U{0002}aa"| || |r0| == |"\U{0002}aaaaaaa\0aa"| || "\U{0002}aa"[|r0|] != "\U{0002}aaaaaaa\0aa"[|r0|];
}
method {:test} Test16() {
var r0 := LongestCommonPrefix("\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaaa", "\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaa");
expect |r0| <= |"\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaaa"| && r0 == "\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaa"| && r0 == "\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaaa"| || |r0| == |"\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaa"| || "\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaaa"[|r0|] != "\U{0006}aaaa\0aaa\U{0002}aaaaaaaaaaa\U{0004}aaaa"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\U{0004}\0a", "\U{0004}\U{0002}aa");
expect |r0| <= |"\U{0004}\0a"| && r0 == "\U{0004}\0a"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aa"| && r0 == "\U{0004}\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0a"| || |r0| == |"\U{0004}\U{0002}aa"| || "\U{0004}\0a"[|r0|] != "\U{0004}\U{0002}aa"[|r0|];
}
