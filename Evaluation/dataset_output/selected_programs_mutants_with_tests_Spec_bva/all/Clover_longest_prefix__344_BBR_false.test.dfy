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

// REPEAT 1 - TIME: 21.8428867 s

method {:test} Test36() {
var r0 := LongestCommonPrefix("\U{0006}\0\U{0004}", "\U{0006}\0\U{0004}\U{0002}");
expect |r0| <= |"\U{0006}\0\U{0004}"| && r0 == "\U{0006}\0\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0006}\0\U{0004}\U{0002}"| && r0 == "\U{0006}\0\U{0004}\U{0002}"[0 .. |r0|];
expect |r0| == |"\U{0006}\0\U{0004}"| || |r0| == |"\U{0006}\0\U{0004}\U{0002}"| || "\U{0006}\0\U{0004}"[|r0|] != "\U{0006}\0\U{0004}\U{0002}"[|r0|];
}
method {:test} Test37() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}a\0aaa\naaaaa\U{000C}", "\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}");
expect |r0| <= |"\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}a\0aaa\naaaaa\U{000C}"| && r0 == "\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}a\0aaa\naaaaa\U{000C}"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}"| && r0 == "\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}a\0aaa\naaaaa\U{000C}"| || |r0| == |"\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}"| || "\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}a\0aaa\naaaaa\U{000C}"[|r0|] != "\U{0002}aaaaaaaaa\U{0004}\U{0006}a\U{0008}"[|r0|];
}
method {:test} Test38() {
var r0 := LongestCommonPrefix("\U{0002}a\U{0004}", "\U{0002}a\0");
expect |r0| <= |"\U{0002}a\U{0004}"| && r0 == "\U{0002}a\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}a\0"| && r0 == "\U{0002}a\0"[0 .. |r0|];
expect |r0| == |"\U{0002}a\U{0004}"| || |r0| == |"\U{0002}a\0"| || "\U{0002}a\U{0004}"[|r0|] != "\U{0002}a\0"[|r0|];
}

// REPEAT 2 - TIME: 23.5729128 s

method {:test} Test39() {
var r0 := LongestCommonPrefix("\na\U{0002}a\U{0006}", "\na\U{0002}a\U{0006}aa\U{0004}aa\U{0008}\U{000C}\0");
expect |r0| <= |"\na\U{0002}a\U{0006}"| && r0 == "\na\U{0002}a\U{0006}"[0 .. |r0|] && |r0| <= |"\na\U{0002}a\U{0006}aa\U{0004}aa\U{0008}\U{000C}\0"| && r0 == "\na\U{0002}a\U{0006}aa\U{0004}aa\U{0008}\U{000C}\0"[0 .. |r0|];
expect |r0| == |"\na\U{0002}a\U{0006}"| || |r0| == |"\na\U{0002}a\U{0006}aa\U{0004}aa\U{0008}\U{000C}\0"| || "\na\U{0002}a\U{0006}"[|r0|] != "\na\U{0002}a\U{0006}aa\U{0004}aa\U{0008}\U{000C}\0"[|r0|];
}
method {:test} Test40() {
var r0 := LongestCommonPrefix("\U{000C}aaaaa\0\U{0004}aa\U{0006}\U{0002}\n\U{0008}a", "\U{000C}aaaaa\0\U{0004}aa");
expect |r0| <= |"\U{000C}aaaaa\0\U{0004}aa\U{0006}\U{0002}\n\U{0008}a"| && r0 == "\U{000C}aaaaa\0\U{0004}aa\U{0006}\U{0002}\n\U{0008}a"[0 .. |r0|] && |r0| <= |"\U{000C}aaaaa\0\U{0004}aa"| && r0 == "\U{000C}aaaaa\0\U{0004}aa"[0 .. |r0|];
expect |r0| == |"\U{000C}aaaaa\0\U{0004}aa\U{0006}\U{0002}\n\U{0008}a"| || |r0| == |"\U{000C}aaaaa\0\U{0004}aa"| || "\U{000C}aaaaa\0\U{0004}aa\U{0006}\U{0002}\n\U{0008}a"[|r0|] != "\U{000C}aaaaa\0\U{0004}aa"[|r0|];
}
method {:test} Test41() {
var r0 := LongestCommonPrefix("\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}\U{0002}\U{0004}");
expect |r0| <= |"\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0006}\U{0002}\U{0004}"| && r0 == "\U{0006}\U{0002}\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0006}\U{0002}\U{0004}"| || "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0006}\U{0002}\U{0004}"[|r0|];
}

// REPEAT 3 - TIME: 25.3180942 s

method {:test} Test42() {
var r0 := LongestCommonPrefix("\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}", "\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}\U{0002}\0\U{0008}");
expect |r0| <= |"\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}"| && r0 == "\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}"[0 .. |r0|] && |r0| <= |"\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}\U{0002}\0\U{0008}"| && r0 == "\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}\U{0002}\0\U{0008}"[0 .. |r0|];
expect |r0| == |"\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}"| || |r0| == |"\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}\U{0002}\0\U{0008}"| || "\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}"[|r0|] != "\U{0004}aaaaaaaaaaaaa\na\U{0006}aaaaaaaaa\U{000C}\U{0002}\0\U{0008}"[|r0|];
}
method {:test} Test43() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa\U{0004}", "\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa");
expect |r0| <= |"\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa\U{0004}"| && r0 == "\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa\U{0004}"| || |r0| == |"\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa"| || "\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa\U{0004}"[|r0|] != "\U{0002}\0aaaaaa\U{0006}aa\U{0008}aaaaaaaaaa"[|r0|];
}
method {:test} Test44() {
var r0 := LongestCommonPrefix("\U{0004}\U{000E}a\U{0006}\U{0008}a", "\U{0004}\U{0010}aaaaa\U{0002}a\0a\U{000C}aa\n");
expect |r0| <= |"\U{0004}\U{000E}a\U{0006}\U{0008}a"| && r0 == "\U{0004}\U{000E}a\U{0006}\U{0008}a"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0010}aaaaa\U{0002}a\0a\U{000C}aa\n"| && r0 == "\U{0004}\U{0010}aaaaa\U{0002}a\0a\U{000C}aa\n"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{000E}a\U{0006}\U{0008}a"| || |r0| == |"\U{0004}\U{0010}aaaaa\U{0002}a\0a\U{000C}aa\n"| || "\U{0004}\U{000E}a\U{0006}\U{0008}a"[|r0|] != "\U{0004}\U{0010}aaaaa\U{0002}a\0a\U{000C}aa\n"[|r0|];
}

// REPEAT 4 - TIME: 27.0710721 s

method {:test} Test45() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test46() {
var r0 := LongestCommonPrefix("\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0006}aa", "\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0006}aa"| && r0 == "\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0006}aa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa"| && r0 == "\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0006}aa"| || |r0| == |"\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa"| || "\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0006}aa"[|r0|] != "\0aaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa"[|r0|];
}
method {:test} Test47() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 5 - TIME: 29.3855165 s

method {:test} Test48() {
var r0 := LongestCommonPrefix("aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa", "aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa");
expect |r0| <= |"aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"| && r0 == "aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"[0 .. |r0|] && |r0| <= |"aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"| && r0 == "aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"[0 .. |r0|];
expect |r0| == |"aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"| || |r0| == |"aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"| || "aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"[|r0|] != "aaa\0aaaaaaa\U{0006}a\U{0002}aaaaa\naa\U{0004}a\U{0008}\U{000C}\U{000E}aa"[|r0|];
}
method {:test} Test49() {
var r0 := LongestCommonPrefix("\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}\U{000E}", "\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}");
expect |r0| <= |"\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}\U{000E}"| && r0 == "\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}\U{000E}"[0 .. |r0|] && |r0| <= |"\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}"| && r0 == "\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}\U{000E}"| || |r0| == |"\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}"| || "\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}\U{000E}"[|r0|] != "\U{0012}aaaaaaaaaaaa\U{0008}a\U{000C}aaaa\U{0002}\0\U{0010}aa\n\U{0006}\U{0004}"[|r0|];
}
method {:test} Test50() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 6 - TIME: 31.8830052 s

method {:test} Test51() {
var r0 := LongestCommonPrefix("\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa", "\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0004}");
expect |r0| <= |"\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0004}"| && r0 == "\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0004}"[0 .. |r0|];
expect |r0| == |"\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0004}"| || "\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0004}"[|r0|];
}
method {:test} Test52() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaa"| || "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaa"[|r0|];
}
method {:test} Test53() {
var r0 := LongestCommonPrefix("\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a");
expect |r0| <= |"\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| && r0 == "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[0 .. |r0|];
expect |r0| == |"\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| || "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[|r0|];
}

// REPEAT 7 - TIME: 34.0819602 s

method {:test} Test54() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test55() {
var r0 := LongestCommonPrefix("\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}aa", "\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}");
expect |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}aa"| && r0 == "\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}aa"[0 .. |r0|] && |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| && r0 == "\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}aa"| || |r0| == |"\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| || "\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}aa"[|r0|] != "\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[|r0|];
}
method {:test} Test56() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}aaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0004}aaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0004}aaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0004}aaaaaaaaaaaaaaaaaaa"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0004}aaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 8 - TIME: 36.6620976 s

method {:test} Test57() {
var r0 := LongestCommonPrefix("\naaaa\U{0004}aaaaa\0aaaa\U{0006}", "\naaaa\U{0004}aaaaa\0aaaa\U{0006}\U{0002}a\U{0008}");
expect |r0| <= |"\naaaa\U{0004}aaaaa\0aaaa\U{0006}"| && r0 == "\naaaa\U{0004}aaaaa\0aaaa\U{0006}"[0 .. |r0|] && |r0| <= |"\naaaa\U{0004}aaaaa\0aaaa\U{0006}\U{0002}a\U{0008}"| && r0 == "\naaaa\U{0004}aaaaa\0aaaa\U{0006}\U{0002}a\U{0008}"[0 .. |r0|];
expect |r0| == |"\naaaa\U{0004}aaaaa\0aaaa\U{0006}"| || |r0| == |"\naaaa\U{0004}aaaaa\0aaaa\U{0006}\U{0002}a\U{0008}"| || "\naaaa\U{0004}aaaaa\0aaaa\U{0006}"[|r0|] != "\naaaa\U{0004}aaaaa\0aaaa\U{0006}\U{0002}a\U{0008}"[|r0|];
}
method {:test} Test58() {
var r0 := LongestCommonPrefix("\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}aa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}");
expect |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}aa"| && r0 == "\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}aa"[0 .. |r0|] && |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}"| && r0 == "\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}aa"| || |r0| == |"\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}"| || "\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}aa"[|r0|] != "\U{0006}aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}a\U{0004}"[|r0|];
}
method {:test} Test59() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 9 - TIME: 39.7344452 s

method {:test} Test60() {
var r0 := LongestCommonPrefix("\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a", "\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a\U{0006}");
expect |r0| <= |"\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a"| && r0 == "\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a\U{0006}"| && r0 == "\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a"| || |r0| == |"\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a\U{0006}"| || "\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a"[|r0|] != "\U{0008}aaaa\0aaaaa\U{0002}aaaa\U{0004}a\U{0006}"[|r0|];
}
method {:test} Test61() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test62() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 42.5979949 s
