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
    break;
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
var r0 := LongestCommonPrefix("\0", "\0");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\0"| || "\0"[|r0|] != "\0"[|r0|];
}
method {:test} Test1() {
var r0 := LongestCommonPrefix("\0", "aa");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"aa"| || "\0"[|r0|] != "aa"[|r0|];
}

// REPEAT 1 - TIME: 2.5742434 s

method {:test} Test2() {
var r0 := LongestCommonPrefix("\0\U{0002}", "\0aa");
expect |r0| <= |"\0\U{0002}"| && r0 == "\0\U{0002}"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}"| || |r0| == |"\0aa"| || "\0\U{0002}"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("aa", "\0");
expect |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|] && |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|];
expect |r0| == |"aa"| || |r0| == |"\0"| || "aa"[|r0|] != "\0"[|r0|];
}

// REPEAT 2 - TIME: 3.7251555 s

method {:test} Test4() {
var r0 := LongestCommonPrefix("\0aaa", "\0aaa");
expect |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|] && |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|];
expect |r0| == |"\0aaa"| || |r0| == |"\0aaa"| || "\0aaa"[|r0|] != "\0aaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\0\U{0006}", "\U{0002}aa\U{0004}");
expect |r0| <= |"\0\U{0006}"| && r0 == "\0\U{0006}"[0 .. |r0|] && |r0| <= |"\U{0002}aa\U{0004}"| && r0 == "\U{0002}aa\U{0004}"[0 .. |r0|];
expect |r0| == |"\0\U{0006}"| || |r0| == |"\U{0002}aa\U{0004}"| || "\0\U{0006}"[|r0|] != "\U{0002}aa\U{0004}"[|r0|];
}

// REPEAT 3 - TIME: 4.9825292 s

method {:test} Test6() {
var r0 := LongestCommonPrefix("\0aaaa", "\0aaaaa");
expect |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|] && |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaa"| || |r0| == |"\0aaaaa"| || "\0aaaa"[|r0|] != "\0aaaaa"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\0a\U{0004}", "\U{0002}a");
expect |r0| <= |"\0a\U{0004}"| && r0 == "\0a\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}a"| && r0 == "\U{0002}a"[0 .. |r0|];
expect |r0| == |"\0a\U{0004}"| || |r0| == |"\U{0002}a"| || "\0a\U{0004}"[|r0|] != "\U{0002}a"[|r0|];
}

// REPEAT 4 - TIME: 6.3771454 s

method {:test} Test8() {
var r0 := LongestCommonPrefix("\0aaaaaa", "\0aaaaaa");
expect |r0| <= |"\0aaaaaa"| && r0 == "\0aaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaa"| && r0 == "\0aaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaa"| || |r0| == |"\0aaaaaa"| || "\0aaaaaa"[|r0|] != "\0aaaaaa"[|r0|];
}
method {:test} Test9() {
var r0 := LongestCommonPrefix("\0", "\U{0004}\U{0002}a");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}a"| && r0 == "\U{0004}\U{0002}a"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\U{0004}\U{0002}a"| || "\0"[|r0|] != "\U{0004}\U{0002}a"[|r0|];
}

// REPEAT 5 - TIME: 7.4915979 s

method {:test} Test10() {
var r0 := LongestCommonPrefix("\U{0002}aaaaa\0a", "\U{0002}aaaaaaaa");
expect |r0| <= |"\U{0002}aaaaa\0a"| && r0 == "\U{0002}aaaaa\0a"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaa"| && r0 == "\U{0002}aaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaa\0a"| || |r0| == |"\U{0002}aaaaaaaa"| || "\U{0002}aaaaa\0a"[|r0|] != "\U{0002}aaaaaaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\U{0004}aaaaaa\U{0002}aaaaa", "\0");
expect |r0| <= |"\U{0004}aaaaaa\U{0002}aaaaa"| && r0 == "\U{0004}aaaaaa\U{0002}aaaaa"[0 .. |r0|] && |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaaa\U{0002}aaaaa"| || |r0| == |"\0"| || "\U{0004}aaaaaa\U{0002}aaaaa"[|r0|] != "\0"[|r0|];
}

// REPEAT 6 - TIME: 8.4043005 s

method {:test} Test12() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaa", "\0aaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaa"| && r0 == "\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaa"| || "\0aaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaa"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\U{0004}aaa", "\U{0002}\0aaaaaaaa");
expect |r0| <= |"\U{0004}aaa"| && r0 == "\U{0004}aaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}aaa"| || |r0| == |"\U{0002}\0aaaaaaaa"| || "\U{0004}aaa"[|r0|] != "\U{0002}\0aaaaaaaa"[|r0|];
}

// REPEAT 7 - TIME: 9.6030253 s

method {:test} Test14() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test15() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaaaa", "\0aaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaa"| || "\U{0002}aaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaa"[|r0|];
}

// REPEAT 8 - TIME: 10.6336285 s

method {:test} Test16() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaa"| || |r0| == |"\U{0002}aaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaa"[|r0|] != "\U{0002}aaaaaaaaaaaaa"[|r0|];
}

// REPEAT 9 - TIME: 11.7774303 s

method {:test} Test18() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("\0aaaaa", "\U{0002}\U{0004}aaaaaaaaa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0004}aaaaaaaaa"| && r0 == "\U{0002}\U{0004}aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\U{0002}\U{0004}aaaaaaaaa"| || "\0aaaaa"[|r0|] != "\U{0002}\U{0004}aaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 12.8819222 s
