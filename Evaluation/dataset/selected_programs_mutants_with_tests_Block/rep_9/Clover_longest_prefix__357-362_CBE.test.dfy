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
