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

method {:test} Test10() {
var r0 := LongestCommonPrefix("\0aaaaaaaa", "\0aaaaaaaaa");
expect |r0| <= |"\0aaaaaaaa"| && r0 == "\0aaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaa"| && r0 == "\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaa"| || |r0| == |"\0aaaaaaaaa"| || "\0aaaaaaaa"[|r0|] != "\0aaaaaaaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\0aaaaaaaa", "\U{0004}aaaaa\U{0002}");
expect |r0| <= |"\0aaaaaaaa"| && r0 == "\0aaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaa\U{0002}"| && r0 == "\U{0004}aaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaa"| || |r0| == |"\U{0004}aaaaa\U{0002}"| || "\0aaaaaaaa"[|r0|] != "\U{0004}aaaaa\U{0002}"[|r0|];
}

// REPEAT 6 - TIME: 7.7707841 s
