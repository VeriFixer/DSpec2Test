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

method {:test} Test45() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}", "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}a\U{000E}a\U{0010}\U{0012}\U{0004}\naaaa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}a\U{000E}a\U{0010}\U{0012}\U{0004}\naaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}a\U{000E}a\U{0010}\U{0012}\U{0004}\naaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}a\U{000E}a\U{0010}\U{0012}\U{0004}\naaaa"| || "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}a\U{000C}a\U{000E}a\U{0010}\U{0012}\U{0004}\naaaa"[|r0|];
}
method {:test} Test46() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa\U{0004}", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa\U{0004}"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa\U{0004}"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa"| || "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa\U{0004}"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0008}aa\naaaaaa"[|r0|];
}
method {:test} Test47() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 5 - TIME: 16.308799 s
