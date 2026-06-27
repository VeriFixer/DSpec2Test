// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if false then |str1| else |str2|;
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

method {:test} Test3() {
var r0 := LongestCommonPrefix("aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa", "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0");
expect |r0| <= |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"| && r0 == "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"| || "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaa\U{0004}aa\U{0002}aaaaaaaaaaaaaa\0"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaa", "\U{0002}\0aaaaaaaaa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaa"| || |r0| == |"\U{0002}\0aaaaaaaaa"| || "\U{0002}\0aaaaaaaaaa"[|r0|] != "\U{0002}\0aaaaaaaaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\U{0006}\U{0004}", "\U{0006}\0\U{0002}\U{0008}");
expect |r0| <= |"\U{0006}\U{0004}"| && r0 == "\U{0006}\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0006}\0\U{0002}\U{0008}"| && r0 == "\U{0006}\0\U{0002}\U{0008}"[0 .. |r0|];
expect |r0| == |"\U{0006}\U{0004}"| || |r0| == |"\U{0006}\0\U{0002}\U{0008}"| || "\U{0006}\U{0004}"[|r0|] != "\U{0006}\0\U{0002}\U{0008}"[|r0|];
}

// REPEAT 2 - TIME: 6.0453017 s
