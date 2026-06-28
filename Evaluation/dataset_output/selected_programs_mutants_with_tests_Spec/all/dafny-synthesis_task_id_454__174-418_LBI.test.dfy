// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    break;
    if s[i] == 'z' || s[i] == 'Z' {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var r0 := ContainsZ("aaaaaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaz"| && ("aaaaaaaaz"[i] == 'z' || "aaaaaaaaz"[i] == 'Z');
}
method {:test} Test1() {
var r0 := ContainsZ("aaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaZ"| && ("aaaaaaaaZ"[i] == 'z' || "aaaaaaaaZ"[i] == 'Z');
}
method {:test} Test2() {
var r0 := ContainsZ("");
expect r0 <==> exists i :: 0 <= i < |""| && (""[i] == 'z' || ""[i] == 'Z');
}

// REPEAT 1 - TIME: 3.8305144 s

method {:test} Test3() {
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("a\0");
expect r0 <==> exists i :: 0 <= i < |"a\0"| && ("a\0"[i] == 'z' || "a\0"[i] == 'Z');
}

// REPEAT 2 - TIME: 5.7155719 s

method {:test} Test6() {
var r0 := ContainsZ("\U{0001}aaaz");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aaaz"| && ("\U{0001}aaaz"[i] == 'z' || "\U{0001}aaaz"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0002}\0Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0Z"| && ("\U{0002}\0Z"[i] == 'z' || "\U{0002}\0Z"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0"| && ("\U{0002}\0"[i] == 'z' || "\U{0002}\0"[i] == 'Z');
}

// REPEAT 3 - TIME: 7.512087 s

method {:test} Test9() {
var r0 := ContainsZ("z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"z\U{0001}"| && ("z\U{0001}"[i] == 'z' || "z\U{0001}"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("\0aZaaa\U{0002}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\0aZaaa\U{0002}\U{0004}"| && ("\0aZaaa\U{0002}\U{0004}"[i] == 'z' || "\0aZaaa\U{0002}\U{0004}"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\U{0004}\U{0002}aa\0aa");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\U{0002}aa\0aa"| && ("\U{0004}\U{0002}aa\0aa"[i] == 'z' || "\U{0004}\U{0002}aa\0aa"[i] == 'Z');
}

// REPEAT 4 - TIME: 9.3876235 s

method {:test} Test12() {
var r0 := ContainsZ("\U{0001}\U{0003}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}\U{0003}z"| && ("\U{0001}\U{0003}z"[i] == 'z' || "\U{0001}\U{0003}z"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\U{0004}a\0\U{0002}a\U{0006}aaZa");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0\U{0002}a\U{0006}aaZa"| && ("\U{0004}a\0\U{0002}a\U{0006}aaZa"[i] == 'z' || "\U{0004}a\0\U{0002}a\U{0006}aaZa"[i] == 'Z');
}
method {:test} Test14() {
var r0 := ContainsZ("\U{0002}aa\0aa");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aa\0aa"| && ("\U{0002}aa\0aa"[i] == 'z' || "\U{0002}aa\0aa"[i] == 'Z');
}

// REPEAT 5 - TIME: 10.9223999 s

method {:test} Test15() {
var r0 := ContainsZ("\0azaaa\U{0002}aa");
expect r0 <==> exists i :: 0 <= i < |"\0azaaa\U{0002}aa"| && ("\0azaaa\U{0002}aa"[i] == 'z' || "\0azaaa\U{0002}aa"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("\U{0006}aa\0a\U{0004}a\U{0008}Z\U{000C}a\U{0002}aaaa\n");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aa\0a\U{0004}a\U{0008}Z\U{000C}a\U{0002}aaaa\n"| && ("\U{0006}aa\0a\U{0004}a\U{0008}Z\U{000C}a\U{0002}aaaa\n"[i] == 'z' || "\U{0006}aa\0a\U{0004}a\U{0008}Z\U{000C}a\U{0002}aaaa\n"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0008}\U{0002}\0a\U{0006}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}\U{0002}\0a\U{0006}\U{0004}"| && ("\U{0008}\U{0002}\0a\U{0006}\U{0004}"[i] == 'z' || "\U{0008}\U{0002}\0a\U{0006}\U{0004}"[i] == 'Z');
}

// REPEAT 6 - TIME: 12.4569827 s

method {:test} Test18() {
var r0 := ContainsZ("\U{0004}azaa\U{0008}a\U{000C}a\U{000E}\U{0006}a\0\na\U{0010}\U{0002}\U{0012}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}azaa\U{0008}a\U{000C}a\U{000E}\U{0006}a\0\na\U{0010}\U{0002}\U{0012}"| && ("\U{0004}azaa\U{0008}a\U{000C}a\U{000E}\U{0006}a\0\na\U{0010}\U{0002}\U{0012}"[i] == 'z' || "\U{0004}azaa\U{0008}a\U{000C}a\U{000E}\U{0006}a\0\na\U{0010}\U{0002}\U{0012}"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{000B}aaaaZ\U{0001}\t\U{0005}\U{0003}\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{000B}aaaaZ\U{0001}\t\U{0005}\U{0003}\U{0007}"| && ("\U{000B}aaaaZ\U{0001}\t\U{0005}\U{0003}\U{0007}"[i] == 'z' || "\U{000B}aaaaZ\U{0001}\t\U{0005}\U{0003}\U{0007}"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("\U{0002}\0aaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0aaa"| && ("\U{0002}\0aaa"[i] == 'z' || "\U{0002}\0aaa"[i] == 'Z');
}

// REPEAT 7 - TIME: 13.9164285 s

method {:test} Test21() {
var r0 := ContainsZ("\taaaaz\U{0001}a\U{0003}\U{0007}\U{0005}");
expect r0 <==> exists i :: 0 <= i < |"\taaaaz\U{0001}a\U{0003}\U{0007}\U{0005}"| && ("\taaaaz\U{0001}a\U{0003}\U{0007}\U{0005}"[i] == 'z' || "\taaaaz\U{0001}a\U{0003}\U{0007}\U{0005}"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("\U{0002}aZ\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aZ\0"| && ("\U{0002}aZ\0"[i] == 'z' || "\U{0002}aZ\0"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0006}aaaa\0\U{0002}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aaaa\0\U{0002}\U{0004}"| && ("\U{0006}aaaa\0\U{0002}\U{0004}"[i] == 'z' || "\U{0006}aaaa\0\U{0002}\U{0004}"[i] == 'Z');
}

// REPEAT 8 - TIME: 15.5762525 s

method {:test} Test24() {
var r0 := ContainsZ("\U{0005}aaa\U{0003}\U{0007}a\U{0001}z\t");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaa\U{0003}\U{0007}a\U{0001}z\t"| && ("\U{0005}aaa\U{0003}\U{0007}a\U{0001}z\t"[i] == 'z' || "\U{0005}aaa\U{0003}\U{0007}a\U{0001}z\t"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("\U{0002}aZ\0a\U{0006}aaa\U{0004}\U{0008}\n");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aZ\0a\U{0006}aaa\U{0004}\U{0008}\n"| && ("\U{0002}aZ\0a\U{0006}aaa\U{0004}\U{0008}\n"[i] == 'z' || "\U{0002}aZ\0a\U{0006}aaa\U{0004}\U{0008}\n"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("\0\U{0002}aaa");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}aaa"| && ("\0\U{0002}aaa"[i] == 'z' || "\0\U{0002}aaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 17.3129567 s

method {:test} Test27() {
var r0 := ContainsZ("\U{0005}aaa\U{0001}aaaz\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaa\U{0001}aaaz\U{0003}"| && ("\U{0005}aaa\U{0001}aaaz\U{0003}"[i] == 'z' || "\U{0005}aaa\U{0001}aaaz\U{0003}"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("Zaaa\0a\U{0008}aaa\U{0002}\U{0006}aa\U{000C}\U{0012}a\U{0016}aa\naa\U{0010}aaa\U{0004}\U{000E}\U{0014}");
expect r0 <==> exists i :: 0 <= i < |"Zaaa\0a\U{0008}aaa\U{0002}\U{0006}aa\U{000C}\U{0012}a\U{0016}aa\naa\U{0010}aaa\U{0004}\U{000E}\U{0014}"| && ("Zaaa\0a\U{0008}aaa\U{0002}\U{0006}aa\U{000C}\U{0012}a\U{0016}aa\naa\U{0010}aaa\U{0004}\U{000E}\U{0014}"[i] == 'z' || "Zaaa\0a\U{0008}aaa\U{0002}\U{0006}aa\U{000C}\U{0012}a\U{0016}aa\naa\U{0010}aaa\U{0004}\U{000E}\U{0014}"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("\U{0006}\U{0004}aaaa\U{0008}\U{0002}\0a\U{000E}\n\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}\U{0004}aaaa\U{0008}\U{0002}\0a\U{000E}\n\U{000C}"| && ("\U{0006}\U{0004}aaaa\U{0008}\U{0002}\0a\U{000E}\n\U{000C}"[i] == 'z' || "\U{0006}\U{0004}aaaa\U{0008}\U{0002}\0a\U{000E}\n\U{000C}"[i] == 'Z');
}

// REPEAT 10 - TIME: 18.9073644 s
