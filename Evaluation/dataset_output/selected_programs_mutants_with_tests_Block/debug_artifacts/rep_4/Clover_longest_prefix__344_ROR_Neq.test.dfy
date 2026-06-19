// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if |str1| != |str2| then |str1| else |str2|;
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
var r0 := LongestCommonPrefix("\0aaaa", "\0aaaaa");
expect |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|] && |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaa"| || |r0| == |"\0aaaaa"| || "\0aaaa"[|r0|] != "\0aaaaa"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\0a\U{0004}", "\U{0002}a");
expect |r0| <= |"\0a\U{0004}"| && r0 == "\0a\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}a"| && r0 == "\U{0002}a"[0 .. |r0|];
expect |r0| == |"\0a\U{0004}"| || |r0| == |"\U{0002}a"| || "\0a\U{0004}"[|r0|] != "\U{0002}a"[|r0|];
}

// REPEAT 4 - TIME: 6.4478359 s
