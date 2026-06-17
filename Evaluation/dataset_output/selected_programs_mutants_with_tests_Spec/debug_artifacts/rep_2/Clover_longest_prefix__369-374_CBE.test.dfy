// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := |str2|;
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
