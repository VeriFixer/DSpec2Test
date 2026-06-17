// Clover_longest_prefix.dfy

method {:testEntry} LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || str1[|prefix|] != str2[|prefix|]
{
  prefix := [];
  var minLength := if |str1| < |str2| then |str1| else |str2|;
  for idx := 0 to minLength
    invariant |prefix| == idx <= minLength <= |str1| && minLength <= |str2|
    invariant |prefix| <= |str1| && prefix == str1[0 .. |prefix|] && |prefix| <= |str2| && prefix == str2[0 .. |prefix|]
  {
    if str1[idx] == str2[idx] {
      return;
    }
    prefix := prefix + [str1[idx]];
  }
}


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

// REPEAT 1 - TIME: 10.9823361 s

method {:test} Test36() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| || "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[|r0|];
}
method {:test} Test37() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"[|r0|];
}
method {:test} Test38() {
var r0 := LongestCommonPrefix("\0\U{0002}", "\0\U{0004}");
expect |r0| <= |"\0\U{0002}"| && r0 == "\0\U{0002}"[0 .. |r0|] && |r0| <= |"\0\U{0004}"| && r0 == "\0\U{0004}"[0 .. |r0|];
expect |r0| == |"\0\U{0002}"| || |r0| == |"\0\U{0004}"| || "\0\U{0002}"[|r0|] != "\0\U{0004}"[|r0|];
}

// REPEAT 2 - TIME: 11.8011738 s

method {:test} Test39() {
var r0 := LongestCommonPrefix("\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n", "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}");
expect |r0| <= |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| && r0 == "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[0 .. |r0|] && |r0| <= |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"| && r0 == "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| || |r0| == |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"| || "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[|r0|] != "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"[|r0|];
}
method {:test} Test40() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"[|r0|];
}
method {:test} Test41() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}\0", "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}\U{0004}\0"| && r0 == "\U{0002}\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}\0"| || |r0| == |"\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0002}\U{0004}\0"[|r0|] != "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 3 - TIME: 12.748235 s

method {:test} Test42() {
var r0 := LongestCommonPrefix("\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}", "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}");
expect |r0| <= |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"| && r0 == "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"[0 .. |r0|] && |r0| <= |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"| && r0 == "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"| || |r0| == |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"| || "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"[|r0|] != "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"[|r0|];
}
method {:test} Test43() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaa\0", "\U{0002}aaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaa\0"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaa\0"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaa\0"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaa\0"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test44() {
var r0 := LongestCommonPrefix("\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 4 - TIME: 13.8597657 s

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

// REPEAT 5 - TIME: 14.9022646 s

method {:test} Test48() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"| || "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"[|r0|];
}
method {:test} Test49() {
var r0 := LongestCommonPrefix("\0a\U{0002}aa\U{0004}aa", "\0a\U{0002}aa\U{0004}a");
expect |r0| <= |"\0a\U{0002}aa\U{0004}aa"| && r0 == "\0a\U{0002}aa\U{0004}aa"[0 .. |r0|] && |r0| <= |"\0a\U{0002}aa\U{0004}a"| && r0 == "\0a\U{0002}aa\U{0004}a"[0 .. |r0|];
expect |r0| == |"\0a\U{0002}aa\U{0004}aa"| || |r0| == |"\0a\U{0002}aa\U{0004}a"| || "\0a\U{0002}aa\U{0004}aa"[|r0|] != "\0a\U{0002}aa\U{0004}a"[|r0|];
}
method {:test} Test50() {
var r0 := LongestCommonPrefix("a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa", "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a");
expect |r0| <= |"a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"| && r0 == "a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"[0 .. |r0|];
expect |r0| == |"a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"| || "a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"[|r0|];
}

// REPEAT 6 - TIME: 16.2623007 s

method {:test} Test51() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"[|r0|];
}
method {:test} Test52() {
var r0 := LongestCommonPrefix("\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa", "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"| || "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"[|r0|] != "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"[|r0|];
}
method {:test} Test53() {
var r0 := LongestCommonPrefix("\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 7 - TIME: 17.4780348 s

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

// REPEAT 8 - TIME: 18.8116946 s

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

// REPEAT 9 - TIME: 20.3551007 s

method {:test} Test60() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test61() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaa"| && r0 == "aaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test62() {
var r0 := LongestCommonPrefix("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 10 - TIME: 21.8433962 s
