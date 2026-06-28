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
var r0 := LongestCommonPrefix("\0aaaaa", "\0aaaaaa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaa"| && r0 == "\0aaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aaaaaa"| || "\0aaaaa"[|r0|] != "\0aaaaaa"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\U{0002}aa", "\0");
expect |r0| <= |"\U{0002}aa"| && r0 == "\U{0002}aa"[0 .. |r0|] && |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|];
expect |r0| == |"\U{0002}aa"| || |r0| == |"\0"| || "\U{0002}aa"[|r0|] != "\0"[|r0|];
}

// REPEAT 4 - TIME: 5.6584752 s
