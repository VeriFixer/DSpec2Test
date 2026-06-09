method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{
  prefix := [];
  var minLength := if |str1| <|str2| then |str1| else |str2|;

  for idx:= 0 to minLength
    invariant |prefix|==idx <=  minLength<=|str1| && minLength<=|str2|
    invariant |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  {
    if str1[idx] != str2[idx] {
      return;
    }
    prefix := prefix + [str1[idx]];
  }
}

method {:test} Test39() {
var r0 := LongestCommonPrefix("\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n", "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}");
expect |r0| <= |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| && r0 == "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[0 .. |r0|] && |r0| <= |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"| && r0 == "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| || |r0| == |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"| || "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[|r0|] != "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"[|r0|];
}
method {:test} Test40() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"[|r0|];
}
method {:test} Test41() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}\0", "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}\U{0004}\0"| && r0 == "\U{0002}\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}\0"| || |r0| == |"\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0002}\U{0004}\0"[|r0|] != "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 3 - TIME: 14.3074849 s
