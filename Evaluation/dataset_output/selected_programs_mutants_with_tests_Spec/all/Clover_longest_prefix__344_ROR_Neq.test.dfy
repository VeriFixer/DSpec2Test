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

// REPEAT 1 - TIME: 3.6494369 s

method {:test} Test3() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaaaa", "\U{0002}\0aaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| || "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}", "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"| && r0 == "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"| || |r0| == |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"| || "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"[|r0|] != "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0004}\0", "\U{0004}\U{0002}");
expect |r0| <= |"\U{0004}\0"| && r0 == "\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}"| && r0 == "\U{0004}\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}\0"| || |r0| == |"\U{0004}\U{0002}"| || "\U{0004}\0"[|r0|] != "\U{0004}\U{0002}"[|r0|];
}

// REPEAT 2 - TIME: 5.5425465 s

method {:test} Test6() {
var r0 := LongestCommonPrefix("\U{0004}aaaaa\0aaaaaaaaa", "\U{0004}aaaaa\0aaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}aaaaa\0aaaaaaaaa"| && r0 == "\U{0004}aaaaa\0aaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaa\0aaaaaaaaa\U{0002}"| && r0 == "\U{0004}aaaaa\0aaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaa\0aaaaaaaaa"| || |r0| == |"\U{0004}aaaaa\0aaaaaaaaa\U{0002}"| || "\U{0004}aaaaa\0aaaaaaaaa"[|r0|] != "\U{0004}aaaaa\0aaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a", "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"| || "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test8() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}a", "\U{0002}\U{0006}\0");
expect |r0| <= |"\U{0002}\U{0004}a"| && r0 == "\U{0002}\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}\0"| && r0 == "\U{0002}\U{0006}\0"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}a"| || |r0| == |"\U{0002}\U{0006}\0"| || "\U{0002}\U{0004}a"[|r0|] != "\U{0002}\U{0006}\0"[|r0|];
}

// REPEAT 3 - TIME: 7.4661073 s

method {:test} Test9() {
var r0 := LongestCommonPrefix("\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\n", "\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\naaaa\U{0002}\U{0004}a\U{0008}");
expect |r0| <= |"\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\n"| && r0 == "\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\n"[0 .. |r0|] && |r0| <= |"\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\naaaa\U{0002}\U{0004}a\U{0008}"| && r0 == "\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\naaaa\U{0002}\U{0004}a\U{0008}"[0 .. |r0|];
expect |r0| == |"\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\n"| || |r0| == |"\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\naaaa\U{0002}\U{0004}a\U{0008}"| || "\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\n"[|r0|] != "\U{000C}aaaaaaaaa\U{0006}aaaaaa\0aa\naaaa\U{0002}\U{0004}a\U{0008}"[|r0|];
}
method {:test} Test10() {
var r0 := LongestCommonPrefix("\U{0008}\0aaaaa\U{0002}a\U{0004}aaaaaa\U{0006}", "\U{0008}\0aaaaa\U{0002}a\U{0004}aaaa");
expect |r0| <= |"\U{0008}\0aaaaa\U{0002}a\U{0004}aaaaaa\U{0006}"| && r0 == "\U{0008}\0aaaaa\U{0002}a\U{0004}aaaaaa\U{0006}"[0 .. |r0|] && |r0| <= |"\U{0008}\0aaaaa\U{0002}a\U{0004}aaaa"| && r0 == "\U{0008}\0aaaaa\U{0002}a\U{0004}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaaaa\U{0002}a\U{0004}aaaaaa\U{0006}"| || |r0| == |"\U{0008}\0aaaaa\U{0002}a\U{0004}aaaa"| || "\U{0008}\0aaaaa\U{0002}a\U{0004}aaaaaa\U{0006}"[|r0|] != "\U{0008}\0aaaaa\U{0002}a\U{0004}aaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\U{0002}\0", "\U{0002}\U{0004}a");
expect |r0| <= |"\U{0002}\0"| && r0 == "\U{0002}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0004}a"| && r0 == "\U{0002}\U{0004}a"[0 .. |r0|];
expect |r0| == |"\U{0002}\0"| || |r0| == |"\U{0002}\U{0004}a"| || "\U{0002}\0"[|r0|] != "\U{0002}\U{0004}a"[|r0|];
}

// REPEAT 4 - TIME: 10.0426448 s

method {:test} Test12() {
var r0 := LongestCommonPrefix("\U{0006}aaaaaaaaaaaaaaa\U{0004}a", "\U{0006}aaaaaaaaaaaaaaa\U{0004}a\U{0002}\0");
expect |r0| <= |"\U{0006}aaaaaaaaaaaaaaa\U{0004}a"| && r0 == "\U{0006}aaaaaaaaaaaaaaa\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0006}aaaaaaaaaaaaaaa\U{0004}a\U{0002}\0"| && r0 == "\U{0006}aaaaaaaaaaaaaaa\U{0004}a\U{0002}\0"[0 .. |r0|];
expect |r0| == |"\U{0006}aaaaaaaaaaaaaaa\U{0004}a"| || |r0| == |"\U{0006}aaaaaaaaaaaaaaa\U{0004}a\U{0002}\0"| || "\U{0006}aaaaaaaaaaaaaaa\U{0004}a"[|r0|] != "\U{0006}aaaaaaaaaaaaaaa\U{0004}a\U{0002}\0"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}aaa\U{0004}aa", "\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}");
expect |r0| <= |"\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}aaa\U{0004}aa"| && r0 == "\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}aaa\U{0004}aa"[0 .. |r0|] && |r0| <= |"\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}"| && r0 == "\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}aaa\U{0004}aa"| || |r0| == |"\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}"| || "\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}aaa\U{0004}aa"[|r0|] != "\U{0008}\0aaaaaaaaaaaa\U{0002}a\U{0006}"[|r0|];
}
method {:test} Test14() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}aa", "\U{0002}\0aa");
expect |r0| <= |"\U{0002}\U{0004}aa"| && r0 == "\U{0002}\U{0004}aa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aa"| && r0 == "\U{0002}\0aa"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}aa"| || |r0| == |"\U{0002}\0aa"| || "\U{0002}\U{0004}aa"[|r0|] != "\U{0002}\0aa"[|r0|];
}

// REPEAT 5 - TIME: 12.114351 s

method {:test} Test15() {
var r0 := LongestCommonPrefix("\U{0004}aaaaaaaa\0aaa", "\U{0004}aaaaaaaa\0aaa\U{0002}");
expect |r0| <= |"\U{0004}aaaaaaaa\0aaa"| && r0 == "\U{0004}aaaaaaaa\0aaa"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaaaaa\0aaa\U{0002}"| && r0 == "\U{0004}aaaaaaaa\0aaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaaaaa\0aaa"| || |r0| == |"\U{0004}aaaaaaaa\0aaa\U{0002}"| || "\U{0004}aaaaaaaa\0aaa"[|r0|] != "\U{0004}aaaaaaaa\0aaa\U{0002}"[|r0|];
}
method {:test} Test16() {
var r0 := LongestCommonPrefix("\U{0002}aaa\0aaaaaaaaaaaaaaaaaaa", "\U{0002}aaa\0");
expect |r0| <= |"\U{0002}aaa\0aaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaa\0aaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaa\0"| && r0 == "\U{0002}aaa\0"[0 .. |r0|];
expect |r0| == |"\U{0002}aaa\0aaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}aaa\0"| || "\U{0002}aaa\0aaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}aaa\0"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}aaa");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0004}aaa"| && r0 == "\0\U{0004}aaa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0004}aaa"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0004}aaa"[|r0|];
}

// REPEAT 6 - TIME: 14.0727894 s

method {:test} Test18() {
var r0 := LongestCommonPrefix("\U{0004}aaaaaaaa\U{0002}aaaaa", "\U{0004}aaaaaaaa\U{0002}aaaaa\0");
expect |r0| <= |"\U{0004}aaaaaaaa\U{0002}aaaaa"| && r0 == "\U{0004}aaaaaaaa\U{0002}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaaaaa\U{0002}aaaaa\0"| && r0 == "\U{0004}aaaaaaaa\U{0002}aaaaa\0"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaaaaa\U{0002}aaaaa"| || |r0| == |"\U{0004}aaaaaaaa\U{0002}aaaaa\0"| || "\U{0004}aaaaaaaa\U{0002}aaaaa"[|r0|] != "\U{0004}aaaaaaaa\U{0002}aaaaa\0"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaa\0aa", "\U{0002}aaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaa\0aa"| && r0 == "\U{0002}aaaaaaaaaaaa\0aa"[0 .. |r0|] && |r0| <= |"\U{0002}aaa"| && r0 == "\U{0002}aaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaa\0aa"| || |r0| == |"\U{0002}aaa"| || "\U{0002}aaaaaaaaaaaa\0aa"[|r0|] != "\U{0002}aaa"[|r0|];
}
method {:test} Test20() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaa"| && r0 == "\U{0004}\U{0002}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaa"[|r0|];
}

// REPEAT 7 - TIME: 16.4662152 s

method {:test} Test21() {
var r0 := LongestCommonPrefix("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}");
expect |r0| <= |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0"| && r0 == "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}"| && r0 == "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0"| || |r0| == |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}"| || "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0"[|r0|] != "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}"[|r0|];
}
method {:test} Test22() {
var r0 := LongestCommonPrefix("\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaaaaa", "\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaaaaa"| && r0 == "\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaa"| && r0 == "\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaa"| || "\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}aaaaaa\U{0002}\0aaaaaaaaaaaaa"[|r0|];
}
method {:test} Test23() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}a");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}a"| && r0 == "\U{0004}\U{0002}a"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}a"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}a"[|r0|];
}

// REPEAT 8 - TIME: 18.5004223 s

method {:test} Test24() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test25() {
var r0 := LongestCommonPrefix("\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa\U{0004}", "\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa");
expect |r0| <= |"\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa\U{0004}"| && r0 == "\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa"| && r0 == "\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa\U{0004}"| || |r0| == |"\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa"| || "\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa\U{0004}"[|r0|] != "\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaa"[|r0|];
}
method {:test} Test26() {
var r0 := LongestCommonPrefix("a\naaaaaaaaaa\U{0002}aaaa\U{0004}aa\U{0006}aaaaaa", "a\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\0aaaaa");
expect |r0| <= |"a\naaaaaaaaaa\U{0002}aaaa\U{0004}aa\U{0006}aaaaaa"| && r0 == "a\naaaaaaaaaa\U{0002}aaaa\U{0004}aa\U{0006}aaaaaa"[0 .. |r0|] && |r0| <= |"a\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\0aaaaa"| && r0 == "a\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\0aaaaa"[0 .. |r0|];
expect |r0| == |"a\naaaaaaaaaa\U{0002}aaaa\U{0004}aa\U{0006}aaaaaa"| || |r0| == |"a\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\0aaaaa"| || "a\naaaaaaaaaa\U{0002}aaaa\U{0004}aa\U{0006}aaaaaa"[|r0|] != "a\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\0aaaaa"[|r0|];
}

// REPEAT 9 - TIME: 20.767306 s

method {:test} Test27() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaa"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaa"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaa"[|r0|];
}
method {:test} Test28() {
var r0 := LongestCommonPrefix("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}", "\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}"| && r0 == "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0006}aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}"| || |r0| == |"\U{0006}aaaaaaaaaaaaaaaaaaaaaa"| || "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}"[|r0|] != "\U{0006}aaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test29() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 23.3224772 s
