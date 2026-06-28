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

method {:test} Test3() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaaaa", "\U{0002}\0aaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaa"| || "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}", "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"| && r0 == "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"| || |r0| == |"\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"| || "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa\U{0002}"[|r0|] != "\U{0004}\0a\U{0006}aaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0004}\0", "\U{0004}\U{0002}");
expect |r0| <= |"\U{0004}\0"| && r0 == "\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}"| && r0 == "\U{0004}\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0004}\0"| || |r0| == |"\U{0004}\U{0002}"| || "\U{0004}\0"[|r0|] != "\U{0004}\U{0002}"[|r0|];
}

// REPEAT 2 - TIME: 5.5425465 s
