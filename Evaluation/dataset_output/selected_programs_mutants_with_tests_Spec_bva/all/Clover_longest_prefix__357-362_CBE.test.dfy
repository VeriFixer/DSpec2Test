// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := |str1|;
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
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa"| || "aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
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
var r0 := LongestCommonPrefix("aaaaaaaaaaaa", "aaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaa"| && r0 == "aaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaa"| || "aaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaa"[|r0|];
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
var r0 := LongestCommonPrefix("aaaaaaaaaaa\0", "aaaaaaaaaaa\U{0002}");
expect |r0| <= |"aaaaaaaaaaa\0"| && r0 == "aaaaaaaaaaa\0"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaa\U{0002}"| && r0 == "aaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaa\0"| || |r0| == |"aaaaaaaaaaa\U{0002}"| || "aaaaaaaaaaa\0"[|r0|] != "aaaaaaaaaaa\U{0002}"[|r0|];
}

// REPEAT 1 - TIME: 15.0282279 s

method {:test} Test36() {
var r0 := LongestCommonPrefix("\U{0008}\0aaaaa\U{0006}aaa", "\U{0008}\0aaaaa\U{0006}aaa\U{0002}aa\U{0004}aaaaaa");
expect |r0| <= |"\U{0008}\0aaaaa\U{0006}aaa"| && r0 == "\U{0008}\0aaaaa\U{0006}aaa"[0 .. |r0|] && |r0| <= |"\U{0008}\0aaaaa\U{0006}aaa\U{0002}aa\U{0004}aaaaaa"| && r0 == "\U{0008}\0aaaaa\U{0006}aaa\U{0002}aa\U{0004}aaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaaaa\U{0006}aaa"| || |r0| == |"\U{0008}\0aaaaa\U{0006}aaa\U{0002}aa\U{0004}aaaaaa"| || "\U{0008}\0aaaaa\U{0006}aaa"[|r0|] != "\U{0008}\0aaaaa\U{0006}aaa\U{0002}aa\U{0004}aaaaaa"[|r0|];
}
method {:test} Test37() {
var r0 := LongestCommonPrefix("\U{0004}\0\U{0002}aaa", "\U{0004}\0\U{0002}aa");
expect |r0| <= |"\U{0004}\0\U{0002}aaa"| && r0 == "\U{0004}\0\U{0002}aaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0\U{0002}aa"| && r0 == "\U{0004}\0\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0\U{0002}aaa"| || |r0| == |"\U{0004}\0\U{0002}aa"| || "\U{0004}\0\U{0002}aaa"[|r0|] != "\U{0004}\0\U{0002}aa"[|r0|];
}
method {:test} Test38() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}\0", "\U{0002}\U{0006}\0");
expect |r0| <= |"\U{0002}\U{0004}\0"| && r0 == "\U{0002}\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}\0"| && r0 == "\U{0002}\U{0006}\0"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}\0"| || |r0| == |"\U{0002}\U{0006}\0"| || "\U{0002}\U{0004}\0"[|r0|] != "\U{0002}\U{0006}\0"[|r0|];
}

// REPEAT 2 - TIME: 16.2122765 s

method {:test} Test39() {
var r0 := LongestCommonPrefix("\U{000E}aaaaaa\U{0004}aaa\U{000C}a", "\U{000E}aaaaaa\U{0004}aaa\U{000C}aaa\U{0002}aa\naa\U{0006}\0a\U{0008}");
expect |r0| <= |"\U{000E}aaaaaa\U{0004}aaa\U{000C}a"| && r0 == "\U{000E}aaaaaa\U{0004}aaa\U{000C}a"[0 .. |r0|] && |r0| <= |"\U{000E}aaaaaa\U{0004}aaa\U{000C}aaa\U{0002}aa\naa\U{0006}\0a\U{0008}"| && r0 == "\U{000E}aaaaaa\U{0004}aaa\U{000C}aaa\U{0002}aa\naa\U{0006}\0a\U{0008}"[0 .. |r0|];
expect |r0| == |"\U{000E}aaaaaa\U{0004}aaa\U{000C}a"| || |r0| == |"\U{000E}aaaaaa\U{0004}aaa\U{000C}aaa\U{0002}aa\naa\U{0006}\0a\U{0008}"| || "\U{000E}aaaaaa\U{0004}aaa\U{000C}a"[|r0|] != "\U{000E}aaaaaa\U{0004}aaa\U{000C}aaa\U{0002}aa\naa\U{0006}\0a\U{0008}"[|r0|];
}
method {:test} Test40() {
var r0 := LongestCommonPrefix("\U{0004}aaaa\0a\U{0002}", "\U{0004}aaaa\0a");
expect |r0| <= |"\U{0004}aaaa\0a\U{0002}"| && r0 == "\U{0004}aaaa\0a\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}aaaa\0a"| && r0 == "\U{0004}aaaa\0a"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaa\0a\U{0002}"| || |r0| == |"\U{0004}aaaa\0a"| || "\U{0004}aaaa\0a\U{0002}"[|r0|] != "\U{0004}aaaa\0a"[|r0|];
}
method {:test} Test41() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}\0", "\U{0002}\U{0006}aa");
expect |r0| <= |"\U{0002}\U{0004}\0"| && r0 == "\U{0002}\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}aa"| && r0 == "\U{0002}\U{0006}aa"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}\0"| || |r0| == |"\U{0002}\U{0006}aa"| || "\U{0002}\U{0004}\0"[|r0|] != "\U{0002}\U{0006}aa"[|r0|];
}

// REPEAT 3 - TIME: 17.4752339 s

method {:test} Test42() {
var r0 := LongestCommonPrefix("\U{0002}aa\U{0004}a", "\U{0002}aa\U{0004}aa\0aaaa\U{0006}");
expect |r0| <= |"\U{0002}aa\U{0004}a"| && r0 == "\U{0002}aa\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0002}aa\U{0004}aa\0aaaa\U{0006}"| && r0 == "\U{0002}aa\U{0004}aa\0aaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0002}aa\U{0004}a"| || |r0| == |"\U{0002}aa\U{0004}aa\0aaaa\U{0006}"| || "\U{0002}aa\U{0004}a"[|r0|] != "\U{0002}aa\U{0004}aa\0aaaa\U{0006}"[|r0|];
}
method {:test} Test43() {
var r0 := LongestCommonPrefix("\U{0010}\0\U{0002}\U{0006}a\na\U{000C}a\U{0004}\U{0008}\U{000E}a", "\U{0010}\0\U{0002}\U{0006}a\na\U{000C}");
expect |r0| <= |"\U{0010}\0\U{0002}\U{0006}a\na\U{000C}a\U{0004}\U{0008}\U{000E}a"| && r0 == "\U{0010}\0\U{0002}\U{0006}a\na\U{000C}a\U{0004}\U{0008}\U{000E}a"[0 .. |r0|] && |r0| <= |"\U{0010}\0\U{0002}\U{0006}a\na\U{000C}"| && r0 == "\U{0010}\0\U{0002}\U{0006}a\na\U{000C}"[0 .. |r0|];
expect |r0| == |"\U{0010}\0\U{0002}\U{0006}a\na\U{000C}a\U{0004}\U{0008}\U{000E}a"| || |r0| == |"\U{0010}\0\U{0002}\U{0006}a\na\U{000C}"| || "\U{0010}\0\U{0002}\U{0006}a\na\U{000C}a\U{0004}\U{0008}\U{000E}a"[|r0|] != "\U{0010}\0\U{0002}\U{0006}a\na\U{000C}"[|r0|];
}
method {:test} Test44() {
var r0 := LongestCommonPrefix("a\U{0018}aaaaaaaaaaa\U{0014}aaaaa\U{0006}\U{0010}aa\na\U{0016}", "a\U{001A}\0\U{0002}a\U{0008}a\U{000C}\U{0004}aa\U{000E}aaaa\U{0012}");
expect |r0| <= |"a\U{0018}aaaaaaaaaaa\U{0014}aaaaa\U{0006}\U{0010}aa\na\U{0016}"| && r0 == "a\U{0018}aaaaaaaaaaa\U{0014}aaaaa\U{0006}\U{0010}aa\na\U{0016}"[0 .. |r0|] && |r0| <= |"a\U{001A}\0\U{0002}a\U{0008}a\U{000C}\U{0004}aa\U{000E}aaaa\U{0012}"| && r0 == "a\U{001A}\0\U{0002}a\U{0008}a\U{000C}\U{0004}aa\U{000E}aaaa\U{0012}"[0 .. |r0|];
expect |r0| == |"a\U{0018}aaaaaaaaaaa\U{0014}aaaaa\U{0006}\U{0010}aa\na\U{0016}"| || |r0| == |"a\U{001A}\0\U{0002}a\U{0008}a\U{000C}\U{0004}aa\U{000E}aaaa\U{0012}"| || "a\U{0018}aaaaaaaaaaa\U{0014}aaaaa\U{0006}\U{0010}aa\na\U{0016}"[|r0|] != "a\U{001A}\0\U{0002}a\U{0008}a\U{000C}\U{0004}aa\U{000E}aaaa\U{0012}"[|r0|];
}

// REPEAT 4 - TIME: 18.6371519 s

method {:test} Test45() {
var r0 := LongestCommonPrefix("aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa", "aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa\naaaa\U{0010}a\0a\U{0012}\U{0004}\U{0006}");
expect |r0| <= |"aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa"| && r0 == "aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa\naaaa\U{0010}a\0a\U{0012}\U{0004}\U{0006}"| && r0 == "aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa\naaaa\U{0010}a\0a\U{0012}\U{0004}\U{0006}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa"| || |r0| == |"aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa\naaaa\U{0010}a\0a\U{0012}\U{0004}\U{0006}"| || "aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa"[|r0|] != "aaaaaaaaa\U{0008}\U{0002}\U{000C}\U{000E}aaa\naaaa\U{0010}a\0a\U{0012}\U{0004}\U{0006}"[|r0|];
}
method {:test} Test46() {
var r0 := LongestCommonPrefix("\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa\U{0006}aaaaaa", "\U{0004}\0aaa\U{0002}aaa");
expect |r0| <= |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa\U{0006}aaaaaa"| && r0 == "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa\U{0006}aaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaa\U{0002}aaa"| && r0 == "\U{0004}\0aaa\U{0002}aaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa\U{0006}aaaaaa"| || |r0| == |"\U{0004}\0aaa\U{0002}aaa"| || "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa\U{0006}aaaaaa"[|r0|] != "\U{0004}\0aaa\U{0002}aaa"[|r0|];
}
method {:test} Test47() {
var r0 := LongestCommonPrefix("\n\0\U{0006}aaaaaa", "\n\U{0002}a\U{0004}aaaa\U{0008}aa");
expect |r0| <= |"\n\0\U{0006}aaaaaa"| && r0 == "\n\0\U{0006}aaaaaa"[0 .. |r0|] && |r0| <= |"\n\U{0002}a\U{0004}aaaa\U{0008}aa"| && r0 == "\n\U{0002}a\U{0004}aaaa\U{0008}aa"[0 .. |r0|];
expect |r0| == |"\n\0\U{0006}aaaaaa"| || |r0| == |"\n\U{0002}a\U{0004}aaaa\U{0008}aa"| || "\n\0\U{0006}aaaaaa"[|r0|] != "\n\U{0002}a\U{0004}aaaa\U{0008}aa"[|r0|];
}

// REPEAT 5 - TIME: 19.840358 s

method {:test} Test48() {
var r0 := LongestCommonPrefix("\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}", "\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}");
expect |r0| <= |"\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"| && r0 == "\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"[0 .. |r0|] && |r0| <= |"\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"| && r0 == "\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"[0 .. |r0|];
expect |r0| == |"\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"| || |r0| == |"\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"| || "\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"[|r0|] != "\n\0\U{0002}aa\U{0006}a\U{0004}a\U{0008}"[|r0|];
}
method {:test} Test49() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}", "\0aaaaaaaaaaa\U{0004}\U{0002}aaaa");
expect |r0| <= |"\0aaaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}"| && r0 == "\0aaaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaa\U{0004}\U{0002}aaaa"| && r0 == "\0aaaaaaaaaaa\U{0004}\U{0002}aaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}"| || |r0| == |"\0aaaaaaaaaaa\U{0004}\U{0002}aaaa"| || "\0aaaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}"[|r0|] != "\0aaaaaaaaaaa\U{0004}\U{0002}aaaa"[|r0|];
}
method {:test} Test50() {
var r0 := LongestCommonPrefix("\0\U{000C}aaa\U{0002}\U{0006}aaaa\naaaaa", "\0\U{000E}aaaaaaaaaa\U{0008}\U{0004}aaaa");
expect |r0| <= |"\0\U{000C}aaa\U{0002}\U{0006}aaaa\naaaaa"| && r0 == "\0\U{000C}aaa\U{0002}\U{0006}aaaa\naaaaa"[0 .. |r0|] && |r0| <= |"\0\U{000E}aaaaaaaaaa\U{0008}\U{0004}aaaa"| && r0 == "\0\U{000E}aaaaaaaaaa\U{0008}\U{0004}aaaa"[0 .. |r0|];
expect |r0| == |"\0\U{000C}aaa\U{0002}\U{0006}aaaa\naaaaa"| || |r0| == |"\0\U{000E}aaaaaaaaaa\U{0008}\U{0004}aaaa"| || "\0\U{000C}aaa\U{0002}\U{0006}aaaa\naaaaa"[|r0|] != "\0\U{000E}aaaaaaaaaa\U{0008}\U{0004}aaaa"[|r0|];
}

// REPEAT 6 - TIME: 21.0756356 s

method {:test} Test51() {
var r0 := LongestCommonPrefix("\U{0004}\0", "\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0002}a\U{0008}aaa");
expect |r0| <= |"\U{0004}\0"| && r0 == "\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0002}a\U{0008}aaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0002}a\U{0008}aaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0002}a\U{0008}aaa"| || "\U{0004}\0"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0002}a\U{0008}aaa"[|r0|];
}
method {:test} Test52() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa\U{0004}", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa\U{0004}"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa\U{0004}"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa\U{0004}"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0aaaaa"[|r0|];
}
method {:test} Test53() {
var r0 := LongestCommonPrefix("a\0aaaaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{000E}", "a\U{0002}aaaaaaaaaaaaaaaaaaa\n\U{0004}aa\U{000C}aaa");
expect |r0| <= |"a\0aaaaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{000E}"| && r0 == "a\0aaaaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{000E}"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaa\n\U{0004}aa\U{000C}aaa"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaa\n\U{0004}aa\U{000C}aaa"[0 .. |r0|];
expect |r0| == |"a\0aaaaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{000E}"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaa\n\U{0004}aa\U{000C}aaa"| || "a\0aaaaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{000E}"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaaaa\n\U{0004}aa\U{000C}aaa"[|r0|];
}

// REPEAT 7 - TIME: 22.2571648 s

method {:test} Test54() {
var r0 := LongestCommonPrefix("aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a", "aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a\U{0004}");
expect |r0| <= |"aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a"| && r0 == "aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a\U{0004}"| && r0 == "aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a\U{0004}"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a"| || |r0| == |"aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a\U{0004}"| || "aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a"[|r0|] != "aaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaa\U{0006}a\U{0004}"[|r0|];
}
method {:test} Test55() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaaa"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaaa"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaa"[|r0|];
}
method {:test} Test56() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 8 - TIME: 23.7373216 s

method {:test} Test57() {
var r0 := LongestCommonPrefix("\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa", "\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa\U{0006}");
expect |r0| <= |"\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa"| && r0 == "\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa"[0 .. |r0|] && |r0| <= |"\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa\U{0006}"| && r0 == "\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa"| || |r0| == |"\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa\U{0006}"| || "\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa"[|r0|] != "\U{0008}aaaaaaaaaa\U{0004}aaaaaaaaa\U{0002}aa\0aaaa\U{0006}"[|r0|];
}
method {:test} Test58() {
var r0 := LongestCommonPrefix("\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}aa", "\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}");
expect |r0| <= |"\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}aa"| && r0 == "\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}aa"[0 .. |r0|] && |r0| <= |"\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"| && r0 == "\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}aa"| || |r0| == |"\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"| || "\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}aa"[|r0|] != "\U{0008}aaaaaaaa\0aaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[|r0|];
}
method {:test} Test59() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 9 - TIME: 25.1636645 s

method {:test} Test60() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test61() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test62() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 26.5966316 s
