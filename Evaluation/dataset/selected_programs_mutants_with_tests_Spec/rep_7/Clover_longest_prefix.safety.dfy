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

method {:test} Test18() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na", "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaaaaaa\U{0008}aaaa\na\0a\U{0002}"[|r0|];
}
method {:test} Test19() {
var r0 := LongestCommonPrefix("aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}", "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}");
expect |r0| <= |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"| && r0 == "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"| && r0 == "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"| || |r0| == |"aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"| || "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}\U{0006}"[|r0|] != "aaaaaaaaaaa\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0008}\U{0004}"[|r0|];
}
method {:test} Test20() {
var r0 := LongestCommonPrefix("\U{0004}\0aaa", "\U{0004}\U{0002}aa");
expect |r0| <= |"\U{0004}\0aaa"| && r0 == "\U{0004}\0aaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aa"| && r0 == "\U{0004}\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaa"| || |r0| == |"\U{0004}\U{0002}aa"| || "\U{0004}\0aaa"[|r0|] != "\U{0004}\U{0002}aa"[|r0|];
}

// REPEAT 7 - TIME: 14.8876132 s
