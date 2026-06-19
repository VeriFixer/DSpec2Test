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

// REPEAT 7 - TIME: 9.936992 s
