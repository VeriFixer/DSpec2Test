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

// REPEAT 6 - TIME: 8.8665081 s
