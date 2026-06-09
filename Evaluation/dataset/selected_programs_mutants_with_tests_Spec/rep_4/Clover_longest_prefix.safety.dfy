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

method {:test} Test9() {
var r0 := LongestCommonPrefix("\U{0002}\0", "\U{0002}\0");
expect |r0| <= |"\U{0002}\0"| && r0 == "\U{0002}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\0"| && r0 == "\U{0002}\0"[0 .. |r0|];
expect |r0| == |"\U{0002}\0"| || |r0| == |"\U{0002}\0"| || "\U{0002}\0"[|r0|] != "\U{0002}\0"[|r0|];
}
method {:test} Test10() {
var r0 := LongestCommonPrefix("\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n", "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"| && r0 == "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"[0 .. |r0|] && |r0| <= |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"| && r0 == "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"| || |r0| == |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"| || "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"[|r0|] != "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\U{0006}\U{0004}a", "\U{0006}\0aaaa\U{0002}aaaa");
expect |r0| <= |"\U{0006}\U{0004}a"| && r0 == "\U{0006}\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0006}\0aaaa\U{0002}aaaa"| && r0 == "\U{0006}\0aaaa\U{0002}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0006}\U{0004}a"| || |r0| == |"\U{0006}\0aaaa\U{0002}aaaa"| || "\U{0006}\U{0004}a"[|r0|] != "\U{0006}\0aaaa\U{0002}aaaa"[|r0|];
}

// REPEAT 4 - TIME: 8.691531 s
