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
