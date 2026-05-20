// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if |str1| > |str2| then |str1| else |str2|;
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

method {:test} Test0() {
var r0 := LongestCommonPrefix("a", "a");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |"a"| || "a"[|r0|] != "a"[|r0|];
}
method {:test} Test1() {
var r0 := LongestCommonPrefix("", "a");
expect |r0| <= |""| && r0 == ""[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |""| || |r0| == |"a"| || ""[|r0|] != "a"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test4() {
var r0 := LongestCommonPrefix("", "");
expect |r0| <= |""| && r0 == ""[0 .. |r0|] && |r0| <= |""| && r0 == ""[0 .. |r0|];
expect |r0| == |""| || |r0| == |""| || ""[|r0|] != ""[|r0|];
}
method {:test} Test6() {
var r0 := LongestCommonPrefix("a", "aa");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |"aa"| || "a"[|r0|] != "aa"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("aa", "a");
expect |r0| <= |"aa"| && r0 == "aa"[0 .. |r0|] && |r0| <= |"a"| && r0 == "a"[0 .. |r0|];
expect |r0| == |"aa"| || |r0| == |"a"| || "aa"[|r0|] != "a"[|r0|];
}
method {:test} Test14() {
var r0 := LongestCommonPrefix("a", "");
expect |r0| <= |"a"| && r0 == "a"[0 .. |r0|] && |r0| <= |""| && r0 == ""[0 .. |r0|];
expect |r0| == |"a"| || |r0| == |""| || "a"[|r0|] != ""[|r0|];
}
method {:test} Test18() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test25() {
var r0 := LongestCommonPrefix("a\0", "a\U{0002}");
expect |r0| <= |"a\0"| && r0 == "a\0"[0 .. |r0|] && |r0| <= |"a\U{0002}"| && r0 == "a\U{0002}"[0 .. |r0|];
expect |r0| == |"a\0"| || |r0| == |"a\U{0002}"| || "a\0"[|r0|] != "a\U{0002}"[|r0|];
}
method {:test} Test26() {
var r0 := LongestCommonPrefix("\0", "\U{0002}");
expect |r0| <= |"\0"| && r0 == "\0"[0 .. |r0|] && |r0| <= |"\U{0002}"| && r0 == "\U{0002}"[0 .. |r0|];
expect |r0| == |"\0"| || |r0| == |"\U{0002}"| || "\0"[|r0|] != "\U{0002}"[|r0|];
}
method {:test} Test33() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test36() {
var r0 := LongestCommonPrefix("\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aa", "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}a\U{0002}");
expect |r0| <= |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aa"| && r0 == "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aa"[0 .. |r0|] && |r0| <= |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}a\U{0002}"| && r0 == "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}a\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aa"| || |r0| == |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}a\U{0002}"| || "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aa"[|r0|] != "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0004}a\U{0002}"[|r0|];
}
method {:test} Test37() {
var r0 := LongestCommonPrefix("\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}a", "\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}");
expect |r0| <= |"\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}a"| && r0 == "\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}a"[0 .. |r0|] && |r0| <= |"\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"| && r0 == "\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}a"| || |r0| == |"\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"| || "\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}a"[|r0|] != "\U{0008}\0aaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[|r0|];
}
method {:test} Test38() {
var r0 := LongestCommonPrefix("\U{0006}\0\U{0004}", "\U{0006}\U{0002}\U{0004}");
expect |r0| <= |"\U{0006}\0\U{0004}"| && r0 == "\U{0006}\0\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0006}\U{0002}\U{0004}"| && r0 == "\U{0006}\U{0002}\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0006}\0\U{0004}"| || |r0| == |"\U{0006}\U{0002}\U{0004}"| || "\U{0006}\0\U{0004}"[|r0|] != "\U{0006}\U{0002}\U{0004}"[|r0|];
}
method {:test} Test39() {
var r0 := LongestCommonPrefix("\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaa", "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}\U{0006}");
expect |r0| <= |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaa"| && r0 == "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| && r0 == "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaa"| || |r0| == |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| || "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaa"[|r0|] != "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[|r0|];
}
method {:test} Test40() {
var r0 := LongestCommonPrefix("\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa\U{0008}", "\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa");
expect |r0| <= |"\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa\U{0008}"| && r0 == "\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa\U{0008}"[0 .. |r0|] && |r0| <= |"\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa"| && r0 == "\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa"[0 .. |r0|];
expect |r0| == |"\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa\U{0008}"| || |r0| == |"\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa"| || "\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa\U{0008}"[|r0|] != "\U{000C}a\U{000E}aaaa\U{0002}aa\U{0004}aaaaaaaa\0aaaaaaaa\U{0006}aaaaaaaaaa\naaaa"[|r0|];
}
method {:test} Test41() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}\0a", "\U{0002}\U{0006}");
expect |r0| <= |"\U{0002}\U{0004}\0a"| && r0 == "\U{0002}\U{0004}\0a"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}"| && r0 == "\U{0002}\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}\0a"| || |r0| == |"\U{0002}\U{0006}"| || "\U{0002}\U{0004}\0a"[|r0|] != "\U{0002}\U{0006}"[|r0|];
}
method {:test} Test42() {
var r0 := LongestCommonPrefix("\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa", "\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa\0a\U{0010}");
expect |r0| <= |"\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa"| && r0 == "\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa\0a\U{0010}"| && r0 == "\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa\0a\U{0010}"[0 .. |r0|];
expect |r0| == |"\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa"| || |r0| == |"\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa\0a\U{0010}"| || "\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa"[|r0|] != "\U{0008}aaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0004}aaa\naaaaaaaa\U{0002}\U{000C}\U{000E}aaaaa\0a\U{0010}"[|r0|];
}
method {:test} Test43() {
var r0 := LongestCommonPrefix("\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}", "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}"| || |r0| == |"\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa"| || "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}"[|r0|] != "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test44() {
var r0 := LongestCommonPrefix("a\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaaaaaa\naaaaaa", "a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}aaaaaaaaaa\U{0008}aaaaaaaa\U{000C}");
expect |r0| <= |"a\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaaaaaa\naaaaaa"| && r0 == "a\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaaaaaa\naaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}aaaaaaaaaa\U{0008}aaaaaaaa\U{000C}"| && r0 == "a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}aaaaaaaaaa\U{0008}aaaaaaaa\U{000C}"[0 .. |r0|];
expect |r0| == |"a\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaaaaaa\naaaaaa"| || |r0| == |"a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}aaaaaaaaaa\U{0008}aaaaaaaa\U{000C}"| || "a\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaaaaaa\naaaaaa"[|r0|] != "a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}aaaaaaaaaa\U{0008}aaaaaaaa\U{000C}"[|r0|];
}
