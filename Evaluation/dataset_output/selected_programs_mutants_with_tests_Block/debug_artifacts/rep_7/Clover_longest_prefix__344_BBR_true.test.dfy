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

method {:test} Test12() {
var r0 := LongestCommonPrefix("\0aaaaaaaaa", "\0aaaaaaaa");
expect |r0| <= |"\0aaaaaaaaa"| && r0 == "\0aaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaa"| && r0 == "\0aaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaa"| || |r0| == |"\0aaaaaaaa"| || "\0aaaaaaaaa"[|r0|] != "\0aaaaaaaa"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\U{0002}\U{0006}", "\U{0004}aaa\0a");
expect |r0| <= |"\U{0002}\U{0006}"| && r0 == "\U{0002}\U{0006}"[0 .. |r0|] && |r0| <= |"\U{0004}aaa\0a"| && r0 == "\U{0004}aaa\0a"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0006}"| || |r0| == |"\U{0004}aaa\0a"| || "\U{0002}\U{0006}"[|r0|] != "\U{0004}aaa\0a"[|r0|];
}

// REPEAT 7 - TIME: 8.7790258 s
