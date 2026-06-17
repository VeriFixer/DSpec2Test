// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' {
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
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}
method {:test} Test2() {
var r0 := ContainsZ("za");
expect r0 <==> exists i :: 0 <= i < |"za"| && ("za"[i] == 'z' || "za"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test9() {
var r0 := ContainsZ("Za");
expect r0 <==> exists i :: 0 <= i < |"Za"| && ("Za"[i] == 'z' || "Za"[i] == 'Z');
}
method {:test} Test14() {
var r0 := ContainsZ("");
expect r0 <==> exists i :: 0 <= i < |""| && (""[i] == 'z' || ""[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("a");
expect r0 <==> exists i :: 0 <= i < |"a"| && ("a"[i] == 'z' || "a"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("aa");
expect r0 <==> exists i :: 0 <= i < |"aa"| && ("aa"[i] == 'z' || "aa"[i] == 'Z');
}

// REPEAT 1 - TIME: 12.7940451 s

method {:test} Test22() {
var r0 := ContainsZ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"| && ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"[i] == 'z' || "a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test24() {
var r0 := ContainsZ("\U{0004}\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && ("\U{0004}\0\U{0002}"[i] == 'z' || "\U{0004}\0\U{0002}"[i] == 'Z');
}

// REPEAT 2 - TIME: 14.3087677 s

method {:test} Test25() {
var r0 := ContainsZ("\U{0003}az\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}az\U{0001}"| && ("\U{0003}az\U{0001}"[i] == 'z' || "\U{0003}az\U{0001}"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}"| && ("aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}"[i] == 'z' || "aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}"[i] == 'Z');
}
method {:test} Test27() {
var r0 := ContainsZ("aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n");
expect r0 <==> exists i :: 0 <= i < |"aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n"| && ("aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n"[i] == 'z' || "aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n"[i] == 'Z');
}

// REPEAT 3 - TIME: 15.9719052 s

method {:test} Test28() {
var r0 := ContainsZ("\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}"| && ("\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}"[i] == 'z' || "\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa"| && ("\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa"[i] == 'z' || "\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa"[i] == 'Z');
}
method {:test} Test30() {
var r0 := ContainsZ("\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}"| && ("\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}"[i] == 'z' || "\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}"[i] == 'Z');
}

// REPEAT 4 - TIME: 17.3676487 s

method {:test} Test31() {
var r0 := ContainsZ("\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa");
expect r0 <==> exists i :: 0 <= i < |"\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa"| && ("\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa"[i] == 'z' || "\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa"[i] == 'Z');
}
method {:test} Test32() {
var r0 := ContainsZ("\U{0003}\U{0001}aZaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}aZaaaa"| && ("\U{0003}\U{0001}aZaaaa"[i] == 'z' || "\U{0003}\U{0001}aZaaaa"[i] == 'Z');
}
method {:test} Test33() {
var r0 := ContainsZ("\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}"| && ("\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}"[i] == 'z' || "\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}"[i] == 'Z');
}

// REPEAT 5 - TIME: 19.4020281 s

method {:test} Test34() {
var r0 := ContainsZ("aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}"| && ("aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}"[i] == 'z' || "aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}"[i] == 'Z');
}
method {:test} Test35() {
var r0 := ContainsZ("aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}");
expect r0 <==> exists i :: 0 <= i < |"aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}"| && ("aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}"[i] == 'z' || "aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}"[i] == 'Z');
}
method {:test} Test36() {
var r0 := ContainsZ("\U{0002}\0\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0\U{0004}"| && ("\U{0002}\0\U{0004}"[i] == 'z' || "\U{0002}\0\U{0004}"[i] == 'Z');
}

// REPEAT 6 - TIME: 21.7651471 s

method {:test} Test37() {
var r0 := ContainsZ("\U{0001}aaz\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aaz\U{0003}"| && ("\U{0001}aaz\U{0003}"[i] == 'z' || "\U{0001}aaz\U{0003}"[i] == 'Z');
}
method {:test} Test38() {
var r0 := ContainsZ("\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}"| && ("\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}"[i] == 'z' || "\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}"[i] == 'Z');
}
method {:test} Test39() {
var r0 := ContainsZ("aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"| && ("aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[i] == 'z' || "aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[i] == 'Z');
}

// REPEAT 7 - TIME: 23.8379961 s

method {:test} Test40() {
var r0 := ContainsZ("aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}"| && ("aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}"[i] == 'z' || "aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}"[i] == 'Z');
}
method {:test} Test41() {
var r0 := ContainsZ("\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa");
expect r0 <==> exists i :: 0 <= i < |"\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa"| && ("\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa"[i] == 'z' || "\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa"[i] == 'Z');
}
method {:test} Test42() {
var r0 := ContainsZ("\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}"| && ("\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}"[i] == 'z' || "\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}"[i] == 'Z');
}

// REPEAT 8 - TIME: 25.6179818 s

method {:test} Test43() {
var r0 := ContainsZ("\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa"| && ("\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa"[i] == 'z' || "\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa"[i] == 'Z');
}
method {:test} Test44() {
var r0 := ContainsZ("aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}"| && ("aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}"[i] == 'z' || "aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}"[i] == 'Z');
}
method {:test} Test45() {
var r0 := ContainsZ("aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa");
expect r0 <==> exists i :: 0 <= i < |"aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa"| && ("aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa"[i] == 'z' || "aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 27.6044458 s

method {:test} Test46() {
var r0 := ContainsZ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa"| && ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa"[i] == 'z' || "aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa"[i] == 'Z');
}
method {:test} Test47() {
var r0 := ContainsZ("\U{0003}aaa\U{0001}aZaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaa\U{0001}aZaa"| && ("\U{0003}aaa\U{0001}aZaa"[i] == 'z' || "\U{0003}aaa\U{0001}aZaa"[i] == 'Z');
}
method {:test} Test48() {
var r0 := ContainsZ("a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa");
expect r0 <==> exists i :: 0 <= i < |"a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa"| && ("a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa"[i] == 'z' || "a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa"[i] == 'Z');
}

// REPEAT 10 - TIME: 30.2102487 s
