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

method {:test} Test21() {
var r0 := LongestCommonPrefix("\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa", "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}");
expect |r0| <= |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"| && r0 == "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"[0 .. |r0|] && |r0| <= |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"| && r0 == "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"| || |r0| == |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"| || "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"[|r0|] != "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"[|r0|];
}
method {:test} Test22() {
var r0 := LongestCommonPrefix("\0aaaaa", "\0aa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aa"| || "\0aaaaa"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test23() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}a");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0004}a"| && r0 == "\0\U{0004}a"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0004}a"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0004}a"[|r0|];
}

// REPEAT 8 - TIME: 17.0169205 s
