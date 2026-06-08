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

method {:test} Test54() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa", "\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa");
expect |r0| <= |"\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa"| && r0 == "\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa"| || "\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa"[|r0|];
}
method {:test} Test55() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa", "aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && r0 == "aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| || |r0| == |"aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| || "aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[|r0|] != "aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test56() {
var r0 := LongestCommonPrefix("\0\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 8 - TIME: 29.3808816 s
