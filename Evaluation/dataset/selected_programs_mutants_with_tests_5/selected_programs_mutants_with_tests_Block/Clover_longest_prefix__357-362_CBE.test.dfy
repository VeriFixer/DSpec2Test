// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := |str1|;
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
var r0 := LongestCommonPrefix("\0", "\0a");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\0a"| && r0 == "\0a"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\0a"| || "\0"[|r0|] != "\0a"[|r0|];
}
method {:test} Test1() {
var r0 := LongestCommonPrefix("\0a", "a");
expect |r0| <= |"\0a"| && r0 == "\0a"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"\0a"| || |r0| == |"a"| || "\0a"[|r0|] != "a"[|r0|];
}
method {:test} Test2() {
var r0 := LongestCommonPrefix("\0aa", "\0a\U{0002}");
expect |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|] && |r0| <= |"\0a\U{0002}"| && r0 == "\0a\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aa"| || |r0| == |"\0a\U{0002}"| || "\0aa"[|r0|] != "\0a\U{0002}"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("\0a", "\U{0002}aa");
expect |r0| <= |"\0a"| && r0 == "\0a"[0 .. |r0|] && |r0| <= |"\U{0002}aa"| && r0 == "\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\0a"| || |r0| == |"\U{0002}aa"| || "\0a"[|r0|] != "\U{0002}aa"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\0aaa", "\0aaa");
expect |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|] && |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|];
expect |r0| == |"\0aaa"| || |r0| == |"\0aaa"| || "\0aaa"[|r0|] != "\0aaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0004}\U{0002}", "\0aa");
expect |r0| <= |"\U{0004}\U{0002}"| && r0 == "\U{0004}\U{0002}"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0002}"| || |r0| == |"\0aa"| || "\U{0004}\U{0002}"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test6() {
var r0 := LongestCommonPrefix("\0aaaa", "\0aaaa");
expect |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|] && |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|];
expect |r0| == |"\0aaaa"| || |r0| == |"\0aaaa"| || "\0aaaa"[|r0|] != "\0aaaa"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\U{0002}", "\U{0004}\0");
expect |r0| <= |"\U{0002}"| && r0 == "\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0"| && r0 == "\U{0004}\0"[0 .. |r0|];
expect |r0| == |"\U{0002}"| || |r0| == |"\U{0004}\0"| || "\U{0002}"[|r0|] != "\U{0004}\0"[|r0|];
}
method {:test} Test8() {
var r0 := LongestCommonPrefix("\0aaaaa", "\0aaaaa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aaaaa"| || "\0aaaaa"[|r0|] != "\0aaaaa"[|r0|];
}
method {:test} Test9() {
var r0 := LongestCommonPrefix("\0aaa", "aaaaaa");
expect |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|] && |r0| <= |"aaaaaa"| && r0 == "aaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaa"| || |r0| == |"aaaaaa"| || "\0aaa"[|r0|] != "aaaaaa"[|r0|];
}
