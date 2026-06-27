// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' && s[i] == 'Z' {
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

// REPEAT 1 - TIME: 4.1679334 s

method {:test} Test3() {
var r0 := ContainsZ("aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}"| && ("aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}"[i] == 'z' || "aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("\0");
expect r0 <==> exists i :: 0 <= i < |"\0"| && ("\0"[i] == 'z' || "\0"[i] == 'Z');
}

// REPEAT 2 - TIME: 5.9673095 s

method {:test} Test6() {
var r0 := ContainsZ("\U{0006}a\U{0002}\0aaaaz\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}a\U{0002}\0aaaaz\U{0004}"| && ("\U{0006}a\U{0002}\0aaaaz\U{0004}"[i] == 'z' || "\U{0006}a\U{0002}\0aaaaz\U{0004}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("Za");
expect r0 <==> exists i :: 0 <= i < |"Za"| && ("Za"[i] == 'z' || "Za"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("\U{0004}\U{0002}aa\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\U{0002}aa\0"| && ("\U{0004}\U{0002}aa\0"[i] == 'z' || "\U{0004}\U{0002}aa\0"[i] == 'Z');
}

// REPEAT 3 - TIME: 7.7259932 s

method {:test} Test9() {
var r0 := ContainsZ("\U{0004}\0zaa\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0zaa\U{0002}"| && ("\U{0004}\0zaa\U{0002}"[i] == 'z' || "\U{0004}\0zaa\U{0002}"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("\U{0002}\0Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0Z"| && ("\U{0002}\0Z"[i] == 'z' || "\U{0002}\0Z"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\U{0002}a\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0"| && ("\U{0002}a\0"[i] == 'z' || "\U{0002}a\0"[i] == 'Z');
}

// REPEAT 4 - TIME: 9.4381737 s

method {:test} Test12() {
var r0 := ContainsZ("\U{0004}azaaa\0\U{0002}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}azaaa\0\U{0002}a"| && ("\U{0004}azaaa\0\U{0002}a"[i] == 'z' || "\U{0004}azaaa\0\U{0002}a"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\U{0002}\0Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0Z"| && ("\U{0002}\0Z"[i] == 'z' || "\U{0002}\0Z"[i] == 'Z');
}
method {:test} Test14() {
var r0 := ContainsZ("\U{0008}\0\U{0004}\U{0002}a\U{0006}\n");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}\0\U{0004}\U{0002}a\U{0006}\n"| && ("\U{0008}\0\U{0004}\U{0002}a\U{0006}\n"[i] == 'z' || "\U{0008}\0\U{0004}\U{0002}a\U{0006}\n"[i] == 'Z');
}

// REPEAT 5 - TIME: 11.0532022 s

method {:test} Test15() {
var r0 := ContainsZ("\0aaza\U{0002}a");
expect r0 <==> exists i :: 0 <= i < |"\0aaza\U{0002}a"| && ("\0aaza\U{0002}a"[i] == 'z' || "\0aaza\U{0002}a"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("\taaaa\U{0005}a\U{0007}a\U{000B}\ra\U{000F}a\U{0001}Zaa\U{0003}aaa\U{0011}");
expect r0 <==> exists i :: 0 <= i < |"\taaaa\U{0005}a\U{0007}a\U{000B}\ra\U{000F}a\U{0001}Zaa\U{0003}aaa\U{0011}"| && ("\taaaa\U{0005}a\U{0007}a\U{000B}\ra\U{000F}a\U{0001}Zaa\U{0003}aaa\U{0011}"[i] == 'z' || "\taaaa\U{0005}a\U{0007}a\U{000B}\ra\U{000F}a\U{0001}Zaa\U{0003}aaa\U{0011}"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0006}a\0aa\U{0004}a\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}a\0aa\U{0004}a\U{0002}"| && ("\U{0006}a\0aa\U{0004}a\U{0002}"[i] == 'z' || "\U{0006}a\0aa\U{0004}a\U{0002}"[i] == 'Z');
}

// REPEAT 6 - TIME: 12.8998122 s

method {:test} Test18() {
var r0 := ContainsZ("\U{0011}aaaaaaaa\r\U{0001}\U{000B}\U{0007}aaza\taa\U{0005}\U{0003}\U{000F}");
expect r0 <==> exists i :: 0 <= i < |"\U{0011}aaaaaaaa\r\U{0001}\U{000B}\U{0007}aaza\taa\U{0005}\U{0003}\U{000F}"| && ("\U{0011}aaaaaaaa\r\U{0001}\U{000B}\U{0007}aaza\taa\U{0005}\U{0003}\U{000F}"[i] == 'z' || "\U{0011}aaaaaaaa\r\U{0001}\U{000B}\U{0007}aaza\taa\U{0005}\U{0003}\U{000F}"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{0003}aaaaaa\U{0001}aaa\U{0013}\U{0011}\U{000B}Z\raaa\U{0005}\U{0007}\U{000F}\U{0015}\t");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaaaaa\U{0001}aaa\U{0013}\U{0011}\U{000B}Z\raaa\U{0005}\U{0007}\U{000F}\U{0015}\t"| && ("\U{0003}aaaaaa\U{0001}aaa\U{0013}\U{0011}\U{000B}Z\raaa\U{0005}\U{0007}\U{000F}\U{0015}\t"[i] == 'z' || "\U{0003}aaaaaa\U{0001}aaa\U{0013}\U{0011}\U{000B}Z\raaa\U{0005}\U{0007}\U{000F}\U{0015}\t"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("\U{0004}aa\U{0002}aa\0a\U{0006}aa\U{0008}aaaa\n");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}aa\U{0002}aa\0a\U{0006}aa\U{0008}aaaa\n"| && ("\U{0004}aa\U{0002}aa\0a\U{0006}aa\U{0008}aaaa\n"[i] == 'z' || "\U{0004}aa\U{0002}aa\0a\U{0006}aa\U{0008}aaaa\n"[i] == 'Z');
}

// REPEAT 7 - TIME: 14.7191475 s

method {:test} Test21() {
var r0 := ContainsZ("\taaaaz\U{0005}a\U{0007}\U{0003}\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\taaaaz\U{0005}a\U{0007}\U{0003}\U{0001}"| && ("\taaaaz\U{0005}a\U{0007}\U{0003}\U{0001}"[i] == 'z' || "\taaaaz\U{0005}a\U{0007}\U{0003}\U{0001}"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("\U{0013}aaaaaaa\U{0003}\t\U{0001}aaZa\U{000B}a\U{0007}aa\U{0005}a\r\U{0011}\U{000F}");
expect r0 <==> exists i :: 0 <= i < |"\U{0013}aaaaaaa\U{0003}\t\U{0001}aaZa\U{000B}a\U{0007}aa\U{0005}a\r\U{0011}\U{000F}"| && ("\U{0013}aaaaaaa\U{0003}\t\U{0001}aaZa\U{000B}a\U{0007}aa\U{0005}a\r\U{0011}\U{000F}"[i] == 'z' || "\U{0013}aaaaaaa\U{0003}\t\U{0001}aaZa\U{000B}a\U{0007}aa\U{0005}a\r\U{0011}\U{000F}"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0002}aaaaaaaaa\n\U{0004}\0a\U{000C}aa\U{000E}aa\U{0006}a\U{0008}\U{0010}\U{0012}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaa\n\U{0004}\0a\U{000C}aa\U{000E}aa\U{0006}a\U{0008}\U{0010}\U{0012}"| && ("\U{0002}aaaaaaaaa\n\U{0004}\0a\U{000C}aa\U{000E}aa\U{0006}a\U{0008}\U{0010}\U{0012}"[i] == 'z' || "\U{0002}aaaaaaaaa\n\U{0004}\0a\U{000C}aa\U{000E}aa\U{0006}a\U{0008}\U{0010}\U{0012}"[i] == 'Z');
}

// REPEAT 8 - TIME: 16.4045335 s

method {:test} Test24() {
var r0 := ContainsZ("za");
expect r0 <==> exists i :: 0 <= i < |"za"| && ("za"[i] == 'z' || "za"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("\U{0003}aaaaaaaaa\t\U{0007}Zaa\U{0001}aaaaa\U{0005}\r\U{000F}\U{0011}\U{000B}aa\U{0013}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaa\t\U{0007}Zaa\U{0001}aaaaa\U{0005}\r\U{000F}\U{0011}\U{000B}aa\U{0013}"| && ("\U{0003}aaaaaaaaa\t\U{0007}Zaa\U{0001}aaaaa\U{0005}\r\U{000F}\U{0011}\U{000B}aa\U{0013}"[i] == 'z' || "\U{0003}aaaaaaaaa\t\U{0007}Zaa\U{0001}aaaaa\U{0005}\r\U{000F}\U{0011}\U{000B}aa\U{0013}"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("\U{0002}aaaaaa\0aa\U{0008}a\U{0006}aaaaaa\U{000C}\U{0004}\n\U{0010}\U{000E}\U{0012}\U{0014}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaa\0aa\U{0008}a\U{0006}aaaaaa\U{000C}\U{0004}\n\U{0010}\U{000E}\U{0012}\U{0014}"| && ("\U{0002}aaaaaa\0aa\U{0008}a\U{0006}aaaaaa\U{000C}\U{0004}\n\U{0010}\U{000E}\U{0012}\U{0014}"[i] == 'z' || "\U{0002}aaaaaa\0aa\U{0008}a\U{0006}aaaaaa\U{000C}\U{0004}\n\U{0010}\U{000E}\U{0012}\U{0014}"[i] == 'Z');
}

// REPEAT 9 - TIME: 18.1242583 s

method {:test} Test27() {
var r0 := ContainsZ("\razaaaa\U{0005}aaa\ta\U{0001}a\U{0003}\U{0007}\U{000B}");
expect r0 <==> exists i :: 0 <= i < |"\razaaaa\U{0005}aaa\ta\U{0001}a\U{0003}\U{0007}\U{000B}"| && ("\razaaaa\U{0005}aaa\ta\U{0001}a\U{0003}\U{0007}\U{000B}"[i] == 'z' || "\razaaaa\U{0005}aaa\ta\U{0001}a\U{0003}\U{0007}\U{000B}"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("\U{0001}aZ\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aZ\U{0003}"| && ("\U{0001}aZ\U{0003}"[i] == 'z' || "\U{0001}aZ\U{0003}"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("\0aaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\0aaaaaaaaa"| && ("\0aaaaaaaaa"[i] == 'z' || "\0aaaaaaaaa"[i] == 'Z');
}

// REPEAT 10 - TIME: 19.9779453 s
