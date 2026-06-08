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
var r0 := LongestCommonPrefix("", "a");
expect |r0| <= |""| && r0 == ""[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |""| || |r0| == |"a"| || ""[|r0|] != "a"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("", "");
expect |r0| <= |""| && r0 == ""[0 .. |r0|] && |r0| <= |""| && r0 == ""[0 .. |r0|];
expect |r0| == |""| || |r0| == |""| || ""[|r0|] != ""[|r0|];
}
method {:test} Test6() {
var r0 := LongestCommonPrefix("a", "aa");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |"aa"| || "a"[|r0|] != "aa"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("aa", "a");
expect |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"aa"| || |r0| == |"a"| || "aa"[|r0|] != "a"[|r0|];
}
method {:test} Test14() {
var r0 := LongestCommonPrefix("a", "");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |""| && r0 == ""[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |""| || "a"[|r0|] != ""[|r0|];
}
method {:test} Test18() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test25() {
var r0 := LongestCommonPrefix("a\0", "a\U{0002}");
expect |r0| <= |"a\0"| && r0 == "a\0"[0 .. |r0|] && |r0| <= |"a\U{0002}"| && r0 == "a\U{0002}"[0 .. |r0|];
expect |r0| == |"a\0"| || |r0| == |"a\U{0002}"| || "a\0"[|r0|] != "a\U{0002}"[|r0|];
}
method {:test} Test26() {
var r0 := LongestCommonPrefix("\0", "\U{0002}");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\U{0002}"| && r0 == "\U{0002}"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\U{0002}"| || "\0"[|r0|] != "\U{0002}"[|r0|];
}
method {:test} Test33() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|r0|];
}

// REPEAT 1 - TIME: 15.2084707 s
