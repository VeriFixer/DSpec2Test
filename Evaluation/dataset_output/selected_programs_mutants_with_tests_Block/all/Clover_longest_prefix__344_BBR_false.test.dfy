// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if false then |str1| else |str2|;
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
var r0 := LongestCommonPrefix("\0", "\0");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\0"| || "\0"[|r0|] != "\0"[|r0|];
}
method {:test} Test1() {
var r0 := LongestCommonPrefix("\0", "aa");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"aa"| || "\0"[|r0|] != "aa"[|r0|];
}

// REPEAT 1 - TIME: 2.2924478 s

method {:test} Test2() {
var r0 := LongestCommonPrefix("\0aa", "\0\U{0002}a");
expect |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|] && |r0| <= |"\0\U{0002}a"| && r0 == "\0\U{0002}a"[0 .. |r0|];
expect |r0| == |"\0aa"| || |r0| == |"\0\U{0002}a"| || "\0aa"[|r0|] != "\0\U{0002}a"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("\0\U{0002}a", "aaaa");
expect |r0| <= |"\0\U{0002}a"| && r0 == "\0\U{0002}a"[0 .. |r0|] && |r0| <= |"aaaa"| && r0 == "aaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}a"| || |r0| == |"aaaa"| || "\0\U{0002}a"[|r0|] != "aaaa"[|r0|];
}

// REPEAT 2 - TIME: 3.3407157 s

method {:test} Test4() {
var r0 := LongestCommonPrefix("\0aaaa", "\0aaa\U{0002}");
expect |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|] && |r0| <= |"\0aaa\U{0002}"| && r0 == "\0aaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aaaa"| || |r0| == |"\0aaa\U{0002}"| || "\0aaaa"[|r0|] != "\0aaa\U{0002}"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0002}a", "\U{0004}\0a");
expect |r0| <= |"\U{0002}a"| && r0 == "\U{0002}a"[0 .. |r0|] && |r0| <= |"\U{0004}\0a"| && r0 == "\U{0004}\0a"[0 .. |r0|];
expect |r0| == |"\U{0002}a"| || |r0| == |"\U{0004}\0a"| || "\U{0002}a"[|r0|] != "\U{0004}\0a"[|r0|];
}

// REPEAT 3 - TIME: 4.4816745 s

method {:test} Test6() {
var r0 := LongestCommonPrefix("\0aaaaa", "\0aaaaaa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaa"| && r0 == "\0aaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aaaaaa"| || "\0aaaaa"[|r0|] != "\0aaaaaa"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\U{0002}aa", "\0");
expect |r0| <= |"\U{0002}aa"| && r0 == "\U{0002}aa"[0 .. |r0|] && |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|];
expect |r0| == |"\U{0002}aa"| || |r0| == |"\0"| || "\U{0002}aa"[|r0|] != "\0"[|r0|];
}

// REPEAT 4 - TIME: 5.6584752 s

method {:test} Test8() {
var r0 := LongestCommonPrefix("\0aaaaaaa", "\0aaaaaaa");
expect |r0| <= |"\0aaaaaaa"| && r0 == "\0aaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaa"| && r0 == "\0aaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaa"| || |r0| == |"\0aaaaaaa"| || "\0aaaaaaa"[|r0|] != "\0aaaaaaa"[|r0|];
}
method {:test} Test9() {
var r0 := LongestCommonPrefix("\U{0002}a", "\U{0004}a\0");
expect |r0| <= |"\U{0002}a"| && r0 == "\U{0002}a"[0 .. |r0|] && |r0| <= |"\U{0004}a\0"| && r0 == "\U{0004}a\0"[0 .. |r0|];
expect |r0| == |"\U{0002}a"| || |r0| == |"\U{0004}a\0"| || "\U{0002}a"[|r0|] != "\U{0004}a\0"[|r0|];
}

// REPEAT 5 - TIME: 6.8575358 s

method {:test} Test10() {
var r0 := LongestCommonPrefix("\0aaaaaaaa", "\0aaaaaaaaa");
expect |r0| <= |"\0aaaaaaaa"| && r0 == "\0aaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaa"| && r0 == "\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaa"| || |r0| == |"\0aaaaaaaaa"| || "\0aaaaaaaa"[|r0|] != "\0aaaaaaaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\0aaaaaaaa", "\U{0004}aaaaa\U{0002}");
expect |r0| <= |"\0aaaaaaaa"| && r0 == "\0aaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaa\U{0002}"| && r0 == "\U{0004}aaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaa"| || |r0| == |"\U{0004}aaaaa\U{0002}"| || "\0aaaaaaaa"[|r0|] != "\U{0004}aaaaa\U{0002}"[|r0|];
}

// REPEAT 6 - TIME: 7.7707841 s

method {:test} Test12() {
var r0 := LongestCommonPrefix("\0aaaaaaaaa", "\0aaaaaaaa");
expect |r0| <= |"\0aaaaaaaaa"| && r0 == "\0aaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaa"| && r0 == "\0aaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaa"| || |r0| == |"\0aaaaaaaa"| || "\0aaaaaaaaa"[|r0|] != "\0aaaaaaaa"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\U{0002}\U{0006}", "\U{0004}aaa\0a");
expect |r0| <= |"\U{0002}\U{0006}"| && r0 == "\U{0002}\U{0006}"[0 .. |r0|] && |r0| <= |"\U{0004}aaa\0a"| && r0 == "\U{0004}aaa\0a"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0006}"| || |r0| == |"\U{0004}aaa\0a"| || "\U{0002}\U{0006}"[|r0|] != "\U{0004}aaa\0a"[|r0|];
}

// REPEAT 7 - TIME: 8.7790258 s

method {:test} Test14() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaa", "\0aaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaa"| && r0 == "\0aaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaa"| && r0 == "\0aaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaa"| || "\0aaaaaaaaaa"[|r0|] != "\0aaaaaaaaaa"[|r0|];
}
method {:test} Test15() {
var r0 := LongestCommonPrefix("\0aaaaaa", "\U{0002}aaaaaaaa");
expect |r0| <= |"\0aaaaaa"| && r0 == "\0aaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaa"| && r0 == "\U{0002}aaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaa"| || |r0| == |"\U{0002}aaaaaaaa"| || "\0aaaaaa"[|r0|] != "\U{0002}aaaaaaaa"[|r0|];
}

// REPEAT 8 - TIME: 9.9523028 s

method {:test} Test16() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaa", "\0aaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaa"| || "\0aaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaa"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\U{0004}a\0aaaa", "\U{0002}aaaaa");
expect |r0| <= |"\U{0004}a\0aaaa"| && r0 == "\U{0004}a\0aaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaa"| && r0 == "\U{0002}aaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}a\0aaaa"| || |r0| == |"\U{0002}aaaaa"| || "\U{0004}a\0aaaa"[|r0|] != "\U{0002}aaaaa"[|r0|];
}

// REPEAT 9 - TIME: 11.1390295 s

method {:test} Test18() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaa", "\0aaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaa"| || "\0aaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaa"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("\0aaaaaaaaa", "aaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaa"| && r0 == "\0aaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaa"| || "\0aaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 12.1892931 s
