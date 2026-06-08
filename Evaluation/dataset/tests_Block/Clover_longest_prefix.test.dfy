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
var r0 := LongestCommonPrefix("\0", "\0a");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\0a"| && r0 == "\0a"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\0a"| || "\0"[|r0|] != "\0a"[|r0|];
}
method {:test} Test1() {
var r0 := LongestCommonPrefix("\0a", "a");
expect |r0| <= |"\0a"| && r0 == "\0a"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"\0a"| || |r0| == |"a"| || "\0a"[|r0|] != "a"[|r0|];
}

// REPEAT 1 - TIME: 2.5218328 s

method {:test} Test2() {
var r0 := LongestCommonPrefix("\0\U{0002}a", "\0aa");
expect |r0| <= |"\0\U{0002}a"| && r0 == "\0\U{0002}a"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}a"| || |r0| == |"\0aa"| || "\0\U{0002}a"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("\U{0004}\U{0002}\0", "\U{0006}aaa");
expect |r0| <= |"\U{0004}\U{0002}\0"| && r0 == "\U{0004}\U{0002}\0"[0 .. |r0|] && |r0| <= |"\U{0006}aaa"| && r0 == "\U{0006}aaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0002}\0"| || |r0| == |"\U{0006}aaa"| || "\U{0004}\U{0002}\0"[|r0|] != "\U{0006}aaa"[|r0|];
}

// REPEAT 2 - TIME: 3.6523588 s

method {:test} Test4() {
var r0 := LongestCommonPrefix("\0aaa", "\0aaaa");
expect |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|] && |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|];
expect |r0| == |"\0aaa"| || |r0| == |"\0aaaa"| || "\0aaa"[|r0|] != "\0aaaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\0\U{0004}", "\U{0002}a");
expect |r0| <= |"\0\U{0004}"| && r0 == "\0\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}a"| && r0 == "\U{0002}a"[0 .. |r0|];
expect |r0| == |"\0\U{0004}"| || |r0| == |"\U{0002}a"| || "\0\U{0004}"[|r0|] != "\U{0002}a"[|r0|];
}

// REPEAT 3 - TIME: 4.7956334 s

method {:test} Test6() {
var r0 := LongestCommonPrefix("\0aaaaa", "\0aaaaa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aaaaa"| || "\0aaaaa"[|r0|] != "\0aaaaa"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\U{0006}\0", "\U{0002}a\U{0004}");
expect |r0| <= |"\U{0006}\0"| && r0 == "\U{0006}\0"[0 .. |r0|] && |r0| <= |"\U{0002}a\U{0004}"| && r0 == "\U{0002}a\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0006}\0"| || |r0| == |"\U{0002}a\U{0004}"| || "\U{0006}\0"[|r0|] != "\U{0002}a\U{0004}"[|r0|];
}

// REPEAT 4 - TIME: 5.9537193 s

method {:test} Test8() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test9() {
var r0 := LongestCommonPrefix("\0aaaaaaa", "aaaaaaa");
expect |r0| <= |"\0aaaaaaa"| && r0 == "\0aaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaa"| && r0 == "aaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaa"| || |r0| == |"aaaaaaa"| || "\0aaaaaaa"[|r0|] != "aaaaaaa"[|r0|];
}

// REPEAT 5 - TIME: 7.1392453 s

method {:test} Test10() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\0aaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 6 - TIME: 8.5122685 s

method {:test} Test12() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\0\U{0008}\U{0002}aaaa", "\U{0004}\U{0006}aaaaaa");
expect |r0| <= |"\0\U{0008}\U{0002}aaaa"| && r0 == "\0\U{0008}\U{0002}aaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0006}aaaaaa"| && r0 == "\U{0004}\U{0006}aaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0008}\U{0002}aaaa"| || |r0| == |"\U{0004}\U{0006}aaaaaa"| || "\0\U{0008}\U{0002}aaaa"[|r0|] != "\U{0004}\U{0006}aaaaaa"[|r0|];
}

// REPEAT 7 - TIME: 10.0414874 s

method {:test} Test14() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test15() {
var r0 := LongestCommonPrefix("\0aaa\U{0006}aaaaa", "\U{0002}aaaa\U{0004}aaaa");
expect |r0| <= |"\0aaa\U{0006}aaaaa"| && r0 == "\0aaa\U{0006}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaa\U{0004}aaaa"| && r0 == "\U{0002}aaaa\U{0004}aaaa"[0 .. |r0|];
expect |r0| == |"\0aaa\U{0006}aaaaa"| || |r0| == |"\U{0002}aaaa\U{0004}aaaa"| || "\0aaa\U{0006}aaaaa"[|r0|] != "\U{0002}aaaa\U{0004}aaaa"[|r0|];
}

// REPEAT 8 - TIME: 11.3650293 s

method {:test} Test16() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "a\U{0004}aaaaaaa");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0004}aaaaaaa"| && r0 == "a\U{0004}aaaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"a\U{0004}aaaaaaa"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "a\U{0004}aaaaaaa"[|r0|];
}

// REPEAT 9 - TIME: 12.4975 s

method {:test} Test18() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\0aaaaaaaaa\U{0002}");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaa\U{0002}"| && r0 == "\0aaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| || |r0| == |"\0aaaaaaaaa\U{0002}"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[|r0|] != "\0aaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 13.559518 s
