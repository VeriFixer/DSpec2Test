// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if true then |str1| else |str2|;
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

method {:test} Test18() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\0aaaaaaaaa\U{0002}");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaa\U{0002}"| && r0 == "\0aaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| || |r0| == |"\0aaaaaaaaa\U{0002}"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[|r0|] != "\0aaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0008}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 13.559518 s
