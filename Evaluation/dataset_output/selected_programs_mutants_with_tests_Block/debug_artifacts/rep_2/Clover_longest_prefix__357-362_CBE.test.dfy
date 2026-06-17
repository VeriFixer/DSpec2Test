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

method {:test} Test2() {
var r0 := LongestCommonPrefix("\0\U{0002}a", "\0aa");
expect |r0| <= |"\0\U{0002}a"| && r0 == "\0\U{0002}a"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}a"| || |r0| == |"\0aa"| || "\0\U{0002}a"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("\U{0004}\U{0002}\0", "\U{0006}aaa");
expect |r0| <= |"\U{0004}\U{0002}\0"| && r0 == "\U{0004}\U{0002}\0"[0 .. |r0|] && |r0| <= |"\U{0006}aaa"| && r0 == "\U{0006}aaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0002}\0"| || |r0| == |"\U{0006}aaa"| || "\U{0004}\U{0002}\0"[|r0|] != "\U{0006}aaa"[|r0|];
}

// REPEAT 2 - TIME: 4.5450392 s
