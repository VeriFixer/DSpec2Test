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

method {:test} Test57() {
var r0 := LongestCommonPrefix("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test58() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test59() {
var r0 := LongestCommonPrefix("a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa", "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"| || "a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 9 - TIME: 20.8648775 s
