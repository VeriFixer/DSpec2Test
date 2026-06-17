// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' <== s[i] == 'Z' {
      result := true;
      break;
    }
  }
}


method {:testEntry} ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z'))
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            break;
        }
    }
}

method {:test} Test0() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'Z');
}
method {:test} Test1() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}
method {:test} Test2() {
var r0 := ContainsZ("");
expect r0 <==> exists i :: 0 <= i < |""| && (""[i] == 'z' || ""[i] == 'Z');
}

// REPEAT 1 - TIME: 3.2241203 s

method {:test} Test3() {
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'Z');
}

// REPEAT 2 - TIME: 5.0773667 s

method {:test} Test6() {
var r0 := ContainsZ("z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"z\U{0001}"| && ("z\U{0001}"[i] == 'z' || "z\U{0001}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("Z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Z\U{0001}"| && ("Z\U{0001}"[i] == 'z' || "Z\U{0001}"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'z' || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'Z');
}

// REPEAT 3 - TIME: 6.947427 s

method {:test} Test9() {
var r0 := ContainsZ("\U{0003}\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}z"| && ("\U{0003}\U{0001}z"[i] == 'z' || "\U{0003}\U{0001}z"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa"| && ("\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa"[i] == 'z' || "\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a");
expect r0 <==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"| && ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"[i] == 'z' || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"[i] == 'Z');
}

// REPEAT 4 - TIME: 8.8288116 s

method {:test} Test12() {
var r0 := ContainsZ("\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza"| && ("\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza"[i] == 'z' || "\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test14() {
var r0 := ContainsZ("\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}"| && ("\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}"[i] == 'z' || "\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}"[i] == 'Z');
}

// REPEAT 5 - TIME: 10.3024009 s

method {:test} Test15() {
var r0 := ContainsZ("\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}"| && ("\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}"[i] == 'z' || "\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0004}a\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\U{0002}\0"| && ("\U{0004}a\U{0002}\0"[i] == 'z' || "\U{0004}a\U{0002}\0"[i] == 'Z');
}

// REPEAT 6 - TIME: 12.2044717 s

method {:test} Test18() {
var r0 := ContainsZ("\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z"| && ("\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z"[i] == 'z' || "\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z"| && ("\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z"[i] == 'z' || "\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}"| && ("\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}"[i] == 'z' || "\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}"[i] == 'Z');
}

// REPEAT 7 - TIME: 14.1338188 s

method {:test} Test21() {
var r0 := ContainsZ("\U{0005}\U{0003}\U{0001}z\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}\U{0003}\U{0001}z\U{0007}"| && ("\U{0005}\U{0003}\U{0001}z\U{0007}"[i] == 'z' || "\U{0005}\U{0003}\U{0001}z\U{0007}"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na"| && ("\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na"[i] == 'z' || "\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}"| && ("\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}"[i] == 'z' || "\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}"[i] == 'Z');
}

// REPEAT 8 - TIME: 15.9928255 s

method {:test} Test24() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("\U{0001}aZ\U{0005}\U{0003}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aZ\U{0005}\U{0003}a"| && ("\U{0001}aZ\U{0005}\U{0003}a"[i] == 'z' || "\U{0001}aZ\U{0005}\U{0003}a"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}"| && ("\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}"[i] == 'z' || "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}"[i] == 'Z');
}

// REPEAT 9 - TIME: 17.834755 s

method {:test} Test27() {
var r0 := ContainsZ("\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}"| && ("\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}"[i] == 'z' || "\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa"| && ("\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa"[i] == 'z' || "\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa"[i] == 'Z');
}

// REPEAT 10 - TIME: 19.4655211 s
