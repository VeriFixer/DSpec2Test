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

method {:test} Test27() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\U{0006}aaaaa\0aa"[|r0|];
}
method {:test} Test28() {
var r0 := LongestCommonPrefix("aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}", "aaaa\U{0006}aaaaaaaa\0");
expect |r0| <= |"aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"| && r0 == "aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"[0 .. |r0|] && |r0| <= |"aaaa\U{0006}aaaaaaaa\0"| && r0 == "aaaa\U{0006}aaaaaaaa\0"[0 .. |r0|];
expect |r0| == |"aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"| || |r0| == |"aaaa\U{0006}aaaaaaaa\0"| || "aaaa\U{0006}aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}"[|r0|] != "aaaa\U{0006}aaaaaaaa\0"[|r0|];
}
method {:test} Test29() {
var r0 := LongestCommonPrefix("a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "a\U{0004}aaaaaa\0aaa");
expect |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0004}aaaaaa\0aaa"| && r0 == "a\U{0004}aaaaaa\0aaa"[0 .. |r0|];
expect |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"a\U{0004}aaaaaa\0aaa"| || "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "a\U{0004}aaaaaa\0aaa"[|r0|];
}

// REPEAT 10 - TIME: 21.5926268 s
