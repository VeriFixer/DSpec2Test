// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if true then |str1| else |str2|;
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

// REPEAT 1 - TIME: 3.7387721 s

method {:test} Test3() {
var r0 := LongestCommonPrefix("aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}a", "aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0006}a\0");
expect |r0| <= |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}a"| && r0 == "aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}a"[0 .. |r0|] && |r0| <= |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0006}a\0"| && r0 == "aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0006}a\0"[0 .. |r0|];
expect |r0| == |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}a"| || |r0| == |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0006}a\0"| || "aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}a"[|r0|] != "aaa\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaa\U{0006}a\0"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0006}\U{0004}", "\U{0006}\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}");
expect |r0| <= |"\U{0006}\U{0004}"| && r0 == "\U{0006}\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0006}\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"| && r0 == "\U{0006}\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"[0 .. |r0|];
expect |r0| == |"\U{0006}\U{0004}"| || |r0| == |"\U{0006}\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"| || "\U{0006}\U{0004}"[|r0|] != "\U{0006}\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"[|r0|];
}

// REPEAT 2 - TIME: 5.5178565 s

method {:test} Test6() {
var r0 := LongestCommonPrefix("\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa", "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}");
expect |r0| <= |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"| && r0 == "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"| && r0 == "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"| || |r0| == |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"| || "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"[|r0|] != "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}", "\n\0aaa");
expect |r0| <= |"\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"| && r0 == "\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"[0 .. |r0|] && |r0| <= |"\n\0aaa"| && r0 == "\n\0aaa"[0 .. |r0|];
expect |r0| == |"\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"| || |r0| == |"\n\0aaa"| || "\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"[|r0|] != "\n\0aaa"[|r0|];
}
method {:test} Test8() {
var r0 := LongestCommonPrefix("\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}", "\U{0004}\U{0008}\0");
expect |r0| <= |"\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0008}\0"| && r0 == "\U{0004}\U{0008}\0"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"| || |r0| == |"\U{0004}\U{0008}\0"| || "\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"[|r0|] != "\U{0004}\U{0008}\0"[|r0|];
}

// REPEAT 3 - TIME: 7.9956735 s

method {:test} Test9() {
var r0 := LongestCommonPrefix("\U{0002}\0", "\U{0002}\0");
expect |r0| <= |"\U{0002}\0"| && r0 == "\U{0002}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\0"| && r0 == "\U{0002}\0"[0 .. |r0|];
expect |r0| == |"\U{0002}\0"| || |r0| == |"\U{0002}\0"| || "\U{0002}\0"[|r0|] != "\U{0002}\0"[|r0|];
}
method {:test} Test10() {
var r0 := LongestCommonPrefix("\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n", "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"| && r0 == "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"[0 .. |r0|] && |r0| <= |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"| && r0 == "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"| || |r0| == |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"| || "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"[|r0|] != "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\U{0006}\U{0004}a", "\U{0006}\0aaaa\U{0002}aaaa");
expect |r0| <= |"\U{0006}\U{0004}a"| && r0 == "\U{0006}\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0006}\0aaaa\U{0002}aaaa"| && r0 == "\U{0006}\0aaaa\U{0002}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0006}\U{0004}a"| || |r0| == |"\U{0006}\0aaaa\U{0002}aaaa"| || "\U{0006}\U{0004}a"[|r0|] != "\U{0006}\0aaaa\U{0002}aaaa"[|r0|];
}

// REPEAT 4 - TIME: 10.5497043 s

method {:test} Test12() {
var r0 := LongestCommonPrefix("\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa", "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}");
expect |r0| <= |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"| && r0 == "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"[0 .. |r0|] && |r0| <= |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"| && r0 == "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"| || |r0| == |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"| || "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"[|r0|] != "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaa"[|r0|];
}
method {:test} Test14() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 5 - TIME: 13.02748 s

method {:test} Test15() {
var r0 := LongestCommonPrefix("\0aaa", "\0aaa");
expect |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|] && |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|];
expect |r0| == |"\0aaa"| || |r0| == |"\0aaa"| || "\0aaa"[|r0|] != "\0aaa"[|r0|];
}
method {:test} Test16() {
var r0 := LongestCommonPrefix("\0aaaaaa", "\0aaa");
expect |r0| <= |"\0aaaaaa"| && r0 == "\0aaaaaa"[0 .. |r0|] && |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaa"| || |r0| == |"\0aaa"| || "\0aaaaaa"[|r0|] != "\0aaa"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaa", "\U{0004}\U{0002}aa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aa"| && r0 == "\U{0004}\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aa"| || "\U{0004}\0aaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aa"[|r0|];
}

// REPEAT 6 - TIME: 15.2866065 s

method {:test} Test18() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na", "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}", "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}");
expect |r0| <= |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"| && r0 == "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"| && r0 == "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"| || |r0| == |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"| || "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"[|r0|] != "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"[|r0|];
}
method {:test} Test20() {
var r0 := LongestCommonPrefix("\U{0004}\0aaa", "\U{0004}\U{0002}aa");
expect |r0| <= |"\U{0004}\0aaa"| && r0 == "\U{0004}\0aaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aa"| && r0 == "\U{0004}\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaa"| || |r0| == |"\U{0004}\U{0002}aa"| || "\U{0004}\0aaa"[|r0|] != "\U{0004}\U{0002}aa"[|r0|];
}

// REPEAT 7 - TIME: 17.0796804 s

method {:test} Test21() {
var r0 := LongestCommonPrefix("\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa", "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}");
expect |r0| <= |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"| && r0 == "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"[0 .. |r0|] && |r0| <= |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"| && r0 == "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"| || |r0| == |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"| || "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"[|r0|] != "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"[|r0|];
}
method {:test} Test22() {
var r0 := LongestCommonPrefix("\0aaaaa", "\0aa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aa"| || "\0aaaaa"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test23() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}a");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0004}a"| && r0 == "\0\U{0004}a"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0004}a"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0004}a"[|r0|];
}

// REPEAT 8 - TIME: 19.2988189 s

method {:test} Test24() {
var r0 := LongestCommonPrefix("\0\U{0002}\U{0004}aa\U{0006}", "\0\U{0002}\U{0004}aa\U{0006}aa");
expect |r0| <= |"\0\U{0002}\U{0004}aa\U{0006}"| && r0 == "\0\U{0002}\U{0004}aa\U{0006}"[0 .. |r0|] && |r0| <= |"\0\U{0002}\U{0004}aa\U{0006}aa"| && r0 == "\0\U{0002}\U{0004}aa\U{0006}aa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}\U{0004}aa\U{0006}"| || |r0| == |"\0\U{0002}\U{0004}aa\U{0006}aa"| || "\0\U{0002}\U{0004}aa\U{0006}"[|r0|] != "\0\U{0002}\U{0004}aa\U{0006}aa"[|r0|];
}
method {:test} Test25() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test26() {
var r0 := LongestCommonPrefix("a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a", "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a");
expect |r0| <= |"a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"| && r0 == "a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"[0 .. |r0|];
expect |r0| == |"a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"| || "a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"[|r0|];
}

// REPEAT 9 - TIME: 21.6269459 s

method {:test} Test27() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"[|r0|];
}
method {:test} Test28() {
var r0 := LongestCommonPrefix("aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}", "aaaa\U{0006}aaaaaaaa\0");
expect |r0| <= |"aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"| && r0 == "aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"[0 .. |r0|] && |r0| <= |"aaaa\U{0006}aaaaaaaa\0"| && r0 == "aaaa\U{0006}aaaaaaaa\0"[0 .. |r0|];
expect |r0| == |"aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"| || |r0| == |"aaaa\U{0006}aaaaaaaa\0"| || "aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"[|r0|] != "aaaa\U{0006}aaaaaaaa\0"[|r0|];
}
method {:test} Test29() {
var r0 := LongestCommonPrefix("a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "a\U{0004}aaaaaa\0aaa");
expect |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0004}aaaaaa\0aaa"| && r0 == "a\U{0004}aaaaaa\0aaa"[0 .. |r0|];
expect |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"a\U{0004}aaaaaa\0aaa"| || "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "a\U{0004}aaaaaa\0aaa"[|r0|];
}

// REPEAT 10 - TIME: 24.1269514 s
