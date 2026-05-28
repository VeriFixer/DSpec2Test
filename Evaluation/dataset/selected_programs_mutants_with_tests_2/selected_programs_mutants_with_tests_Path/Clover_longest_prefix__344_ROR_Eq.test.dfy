// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if |str1| == |str2| then |str1| else |str2|;
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
var r0 := LongestCommonPrefix("a", "aa");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |"aa"| || "a"[|r0|] != "aa"[|r0|];
}
method {:test} Test1() {
var r0 := LongestCommonPrefix("a\0", "a\U{0002}a");
expect |r0| <= |"a\0"| && r0 == "a\0"[0 .. |r0|] && |r0| <= |"a\U{0002}a"| && r0 == "a\U{0002}a"[0 .. |r0|];
expect |r0| == |"a\0"| || |r0| == |"a\U{0002}a"| || "a\0"[|r0|] != "a\U{0002}a"[|r0|];
}
method {:test} Test2() {
var r0 := LongestCommonPrefix("a", "a");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |"a"| || "a"[|r0|] != "a"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("a\0", "a\U{0002}");
expect |r0| <= |"a\0"| && r0 == "a\0"[0 .. |r0|] && |r0| <= |"a\U{0002}"| && r0 == "a\U{0002}"[0 .. |r0|];
expect |r0| == |"a\0"| || |r0| == |"a\U{0002}"| || "a\0"[|r0|] != "a\U{0002}"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\0", "\0a\U{0002}\U{0004}");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\0a\U{0002}\U{0004}"| && r0 == "\0a\U{0002}\U{0004}"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\0a\U{0002}\U{0004}"| || "\0"[|r0|] != "\0a\U{0002}\U{0004}"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\n\U{0006}aaaaaaaaaaa\U{0002}", "\n\U{0008}a\U{0004}aaaaaaa\0aaa");
expect |r0| <= |"\n\U{0006}aaaaaaaaaaa\U{0002}"| && r0 == "\n\U{0006}aaaaaaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\n\U{0008}a\U{0004}aaaaaaa\0aaa"| && r0 == "\n\U{0008}a\U{0004}aaaaaaa\0aaa"[0 .. |r0|];
expect |r0| == |"\n\U{0006}aaaaaaaaaaa\U{0002}"| || |r0| == |"\n\U{0008}a\U{0004}aaaaaaa\0aaa"| || "\n\U{0006}aaaaaaaaaaa\U{0002}"[|r0|] != "\n\U{0008}a\U{0004}aaaaaaa\0aaa"[|r0|];
}
method {:test} Test6() {
var r0 := LongestCommonPrefix("\0a\U{0002}\U{0004}", "\0a\U{0002}\U{0004}");
expect |r0| <= |"\0a\U{0002}\U{0004}"| && r0 == "\0a\U{0002}\U{0004}"[0 .. |r0|] && |r0| <= |"\0a\U{0002}\U{0004}"| && r0 == "\0a\U{0002}\U{0004}"[0 .. |r0|];
expect |r0| == |"\0a\U{0002}\U{0004}"| || |r0| == |"\0a\U{0002}\U{0004}"| || "\0a\U{0002}\U{0004}"[|r0|] != "\0a\U{0002}\U{0004}"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\n\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\n\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0");
expect |r0| <= |"\n\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\n\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\n\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0"| && r0 == "\n\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0"[0 .. |r0|];
expect |r0| == |"\n\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\n\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0"| || "\n\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\n\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0"[|r0|];
}
