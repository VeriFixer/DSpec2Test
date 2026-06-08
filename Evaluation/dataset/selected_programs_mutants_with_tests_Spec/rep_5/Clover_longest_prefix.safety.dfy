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

method {:test} Test12() {
var r0 := LongestCommonPrefix("\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa", "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}");
expect |r0| <= |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"| && r0 == "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"[0 .. |r0|] && |r0| <= |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"| && r0 == "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"| || |r0| == |"\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"| || "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaa"[|r0|] != "\U{000C}\0aa\U{0004}\n\U{0002}a\U{0008}aaaaaaaaaaaa\U{0006}"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaa"[|r0|];
}
method {:test} Test14() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 5 - TIME: 12.1728956 s
