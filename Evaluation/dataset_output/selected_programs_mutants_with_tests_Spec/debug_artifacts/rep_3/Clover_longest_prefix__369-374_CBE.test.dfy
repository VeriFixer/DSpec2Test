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

method {:test} Test6() {
var r0 := LongestCommonPrefix("\U{0004}aaaaa\0aaaaaaaaa", "\U{0004}aaaaa\0aaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}aaaaa\0aaaaaaaaa"| && r0 == "\U{0004}aaaaa\0aaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaa\0aaaaaaaaa\U{0002}"| && r0 == "\U{0004}aaaaa\0aaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaa\0aaaaaaaaa"| || |r0| == |"\U{0004}aaaaa\0aaaaaaaaa\U{0002}"| || "\U{0004}aaaaa\0aaaaaaaaa"[|r0|] != "\U{0004}aaaaa\0aaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a", "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"| || "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}a"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test8() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}a", "\U{0002}\U{0006}\0");
expect |r0| <= |"\U{0002}\U{0004}a"| && r0 == "\U{0002}\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}\0"| && r0 == "\U{0002}\U{0006}\0"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}a"| || |r0| == |"\U{0002}\U{0006}\0"| || "\U{0002}\U{0004}a"[|r0|] != "\U{0002}\U{0006}\0"[|r0|];
}

// REPEAT 3 - TIME: 7.4661073 s
