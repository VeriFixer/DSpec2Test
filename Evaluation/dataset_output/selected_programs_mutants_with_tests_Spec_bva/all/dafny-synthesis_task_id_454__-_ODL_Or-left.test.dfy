// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'Z' {
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
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}
method {:test} Test2() {
var r0 := ContainsZ("za");
expect r0 <==> exists i :: 0 <= i < |"za"| && ("za"[i] == 'z' || "za"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("aaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaZ"| && ("aaaaaaaaZ"[i] == 'z' || "aaaaaaaaZ"[i] == 'Z');
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

// REPEAT 1 - TIME: 17.4939757 s

method {:test} Test22() {
var r0 := ContainsZ("\U{0002}\0z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0z"| && ("\U{0002}\0z"[i] == 'z' || "\U{0002}\0z"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0003}aaaaaaaZ\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaaaaaaZ\U{0001}"| && ("\U{0003}aaaaaaaZ\U{0001}"[i] == 'z' || "\U{0003}aaaaaaaZ\U{0001}"[i] == 'Z');
}
method {:test} Test24() {
var r0 := ContainsZ("\U{0002}aaaaaaa\0\U{0006}aaaaaaaaaaa\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaa\0\U{0006}aaaaaaaaaaa\U{0004}"| && ("\U{0002}aaaaaaa\0\U{0006}aaaaaaaaaaa\U{0004}"[i] == 'z' || "\U{0002}aaaaaaa\0\U{0006}aaaaaaaaaaa\U{0004}"[i] == 'Z');
}

// REPEAT 2 - TIME: 19.3230059 s

method {:test} Test25() {
var r0 := ContainsZ("\U{0002}\0aaaaz");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0aaaaz"| && ("\U{0002}\0aaaaz"[i] == 'z' || "\U{0002}\0aaaaz"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("\U{0007}a\U{0003}\U{0001}aaaaZ\U{0005}");
expect r0 <==> exists i :: 0 <= i < |"\U{0007}a\U{0003}\U{0001}aaaaZ\U{0005}"| && ("\U{0007}a\U{0003}\U{0001}aaaaZ\U{0005}"[i] == 'z' || "\U{0007}a\U{0003}\U{0001}aaaaZ\U{0005}"[i] == 'Z');
}
method {:test} Test27() {
var r0 := ContainsZ("\U{0002}aaaaaaa\0\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaa\0\U{0004}"| && ("\U{0002}aaaaaaa\0\U{0004}"[i] == 'z' || "\U{0002}aaaaaaa\0\U{0004}"[i] == 'Z');
}

// REPEAT 3 - TIME: 21.1347595 s

method {:test} Test28() {
var r0 := ContainsZ("\U{0004}aaza\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}aaza\U{0002}\0"| && ("\U{0004}aaza\U{0002}\0"[i] == 'z' || "\U{0004}aaza\U{0002}\0"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test30() {
var r0 := ContainsZ("\U{0002}a\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0"| && ("\U{0002}a\0"[i] == 'z' || "\U{0002}a\0"[i] == 'Z');
}

// REPEAT 4 - TIME: 22.8729631 s

method {:test} Test31() {
var r0 := ContainsZ("\U{0004}\U{0002}z\0aaaaaaaaaaaaaaaaaa\U{0008}aaaaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\U{0002}z\0aaaaaaaaaaaaaaaaaa\U{0008}aaaaa\U{0006}"| && ("\U{0004}\U{0002}z\0aaaaaaaaaaaaaaaaaa\U{0008}aaaaa\U{0006}"[i] == 'z' || "\U{0004}\U{0002}z\0aaaaaaaaaaaaaaaaaa\U{0008}aaaaa\U{0006}"[i] == 'Z');
}
method {:test} Test32() {
var r0 := ContainsZ("aaaaaaaaa\U{0007}\U{000B}aaa\U{0003}Z\t\U{0001}a\U{0005}aa\r");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaa\U{0007}\U{000B}aaa\U{0003}Z\t\U{0001}a\U{0005}aa\r"| && ("aaaaaaaaa\U{0007}\U{000B}aaa\U{0003}Z\t\U{0001}a\U{0005}aa\r"[i] == 'z' || "aaaaaaaaa\U{0007}\U{000B}aaa\U{0003}Z\t\U{0001}a\U{0005}aa\r"[i] == 'Z');
}
method {:test} Test33() {
var r0 := ContainsZ("\U{0006}aa\U{0002}a\U{0004}aaa\naaa\U{0008}aaa\0aaaa\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aa\U{0002}a\U{0004}aaa\naaa\U{0008}aaa\0aaaa\U{000C}"| && ("\U{0006}aa\U{0002}a\U{0004}aaa\naaa\U{0008}aaa\0aaaa\U{000C}"[i] == 'z' || "\U{0006}aa\U{0002}a\U{0004}aaa\naaa\U{0008}aaa\0aaaa\U{000C}"[i] == 'Z');
}

// REPEAT 5 - TIME: 24.8643199 s

method {:test} Test34() {
var r0 := ContainsZ("\U{000B}a\U{0001}a\U{0003}zaa\t\U{0005}\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{000B}a\U{0001}a\U{0003}zaa\t\U{0005}\U{0007}"| && ("\U{000B}a\U{0001}a\U{0003}zaa\t\U{0005}\U{0007}"[i] == 'z' || "\U{000B}a\U{0001}a\U{0003}zaa\t\U{0005}\U{0007}"[i] == 'Z');
}
method {:test} Test35() {
var r0 := ContainsZ("\U{0007}aaaaZaa\U{0005}\U{0001}\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0007}aaaaZaa\U{0005}\U{0001}\U{0003}"| && ("\U{0007}aaaaZaa\U{0005}\U{0001}\U{0003}"[i] == 'z' || "\U{0007}aaaaZaa\U{0005}\U{0001}\U{0003}"[i] == 'Z');
}
method {:test} Test36() {
var r0 := ContainsZ("\U{0006}aaaa\U{0002}\U{0004}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aaaa\U{0002}\U{0004}\0"| && ("\U{0006}aaaa\U{0002}\U{0004}\0"[i] == 'z' || "\U{0006}aaaa\U{0002}\U{0004}\0"[i] == 'Z');
}

// REPEAT 6 - TIME: 27.1751928 s

method {:test} Test37() {
var r0 := ContainsZ("\U{0003}az\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}az\U{0001}"| && ("\U{0003}az\U{0001}"[i] == 'z' || "\U{0003}az\U{0001}"[i] == 'Z');
}
method {:test} Test38() {
var r0 := ContainsZ("\ta\U{0003}a\U{0005}aaa\U{0011}a\ra\U{0001}aZ\U{000B}a\U{0007}\U{0015}\U{0013}aa\U{000F}a");
expect r0 <==> exists i :: 0 <= i < |"\ta\U{0003}a\U{0005}aaa\U{0011}a\ra\U{0001}aZ\U{000B}a\U{0007}\U{0015}\U{0013}aa\U{000F}a"| && ("\ta\U{0003}a\U{0005}aaa\U{0011}a\ra\U{0001}aZ\U{000B}a\U{0007}\U{0015}\U{0013}aa\U{000F}a"[i] == 'z' || "\ta\U{0003}a\U{0005}aaa\U{0011}a\ra\U{0001}aZ\U{000B}a\U{0007}\U{0015}\U{0013}aa\U{000F}a"[i] == 'Z');
}
method {:test} Test39() {
var r0 := ContainsZ("aaa\U{0002}aaaaaaaaaa\U{0004}aaaa\0a\n\U{0006}\U{000C}aaaa\U{0008}\U{000E}");
expect r0 <==> exists i :: 0 <= i < |"aaa\U{0002}aaaaaaaaaa\U{0004}aaaa\0a\n\U{0006}\U{000C}aaaa\U{0008}\U{000E}"| && ("aaa\U{0002}aaaaaaaaaa\U{0004}aaaa\0a\n\U{0006}\U{000C}aaaa\U{0008}\U{000E}"[i] == 'z' || "aaa\U{0002}aaaaaaaaaa\U{0004}aaaa\0a\n\U{0006}\U{000C}aaaa\U{0008}\U{000E}"[i] == 'Z');
}

// REPEAT 7 - TIME: 29.18924 s

method {:test} Test40() {
var r0 := ContainsZ("\U{000B}azaa\U{0001}a\U{0005}a\t\U{0003}\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{000B}azaa\U{0001}a\U{0005}a\t\U{0003}\U{0007}"| && ("\U{000B}azaa\U{0001}a\U{0005}a\t\U{0003}\U{0007}"[i] == 'z' || "\U{000B}azaa\U{0001}a\U{0005}a\t\U{0003}\U{0007}"[i] == 'Z');
}
method {:test} Test41() {
var r0 := ContainsZ("aaaaaaa\U{0001}\U{000B}aZaaaaa\U{0005}aa\U{0003}a\U{0011}\U{0013}\U{000F}a\t\U{0007}\r");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaa\U{0001}\U{000B}aZaaaaa\U{0005}aa\U{0003}a\U{0011}\U{0013}\U{000F}a\t\U{0007}\r"| && ("aaaaaaa\U{0001}\U{000B}aZaaaaa\U{0005}aa\U{0003}a\U{0011}\U{0013}\U{000F}a\t\U{0007}\r"[i] == 'z' || "aaaaaaa\U{0001}\U{000B}aZaaaaa\U{0005}aa\U{0003}a\U{0011}\U{0013}\U{000F}a\t\U{0007}\r"[i] == 'Z');
}
method {:test} Test42() {
var r0 := ContainsZ("\U{0004}\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && ("\U{0004}\0\U{0002}"[i] == 'z' || "\U{0004}\0\U{0002}"[i] == 'Z');
}

// REPEAT 8 - TIME: 31.1593167 s

method {:test} Test43() {
var r0 := ContainsZ("\U{0015}aaaaa\U{0003}aaza\U{000F}aa\raaaa\U{0007}a\t\U{0001}\U{0013}\U{0005}a\U{0011}\U{000B}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0015}aaaaa\U{0003}aaza\U{000F}aa\raaaa\U{0007}a\t\U{0001}\U{0013}\U{0005}a\U{0011}\U{000B}a"| && ("\U{0015}aaaaa\U{0003}aaza\U{000F}aa\raaaa\U{0007}a\t\U{0001}\U{0013}\U{0005}a\U{0011}\U{000B}a"[i] == 'z' || "\U{0015}aaaaa\U{0003}aaza\U{000F}aa\raaaa\U{0007}a\t\U{0001}\U{0013}\U{0005}a\U{0011}\U{000B}a"[i] == 'Z');
}
method {:test} Test44() {
var r0 := ContainsZ("\U{0007}aa\taaa\U{0001}\U{000F}\U{0003}Za\U{0015}aaa\U{0005}aa\U{0011}aa\U{0017}\U{0013}a\ra\U{000B}");
expect r0 <==> exists i :: 0 <= i < |"\U{0007}aa\taaa\U{0001}\U{000F}\U{0003}Za\U{0015}aaa\U{0005}aa\U{0011}aa\U{0017}\U{0013}a\ra\U{000B}"| && ("\U{0007}aa\taaa\U{0001}\U{000F}\U{0003}Za\U{0015}aaa\U{0005}aa\U{0011}aa\U{0017}\U{0013}a\ra\U{000B}"[i] == 'z' || "\U{0007}aa\taaa\U{0001}\U{000F}\U{0003}Za\U{0015}aaa\U{0005}aa\U{0011}aa\U{0017}\U{0013}a\ra\U{000B}"[i] == 'Z');
}
method {:test} Test45() {
var r0 := ContainsZ("\U{0004}aaaaaaaa\U{0002}\0aaaa\U{0006}aa\U{000C}aaa\U{000E}\U{0010}aa\n\U{0008}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}aaaaaaaa\U{0002}\0aaaa\U{0006}aa\U{000C}aaa\U{000E}\U{0010}aa\n\U{0008}a"| && ("\U{0004}aaaaaaaa\U{0002}\0aaaa\U{0006}aa\U{000C}aaa\U{000E}\U{0010}aa\n\U{0008}a"[i] == 'z' || "\U{0004}aaaaaaaa\U{0002}\0aaaa\U{0006}aa\U{000C}aaa\U{000E}\U{0010}aa\n\U{0008}a"[i] == 'Z');
}

// REPEAT 9 - TIME: 33.301087 s

method {:test} Test46() {
var r0 := ContainsZ("\U{0003}aaaaaaaaa\U{0001}az");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaa\U{0001}az"| && ("\U{0003}aaaaaaaaa\U{0001}az"[i] == 'z' || "\U{0003}aaaaaaaaa\U{0001}az"[i] == 'Z');
}
method {:test} Test47() {
var r0 := ContainsZ("aa\U{0003}aaaaaaaaZaaaaaaaa\U{0001}aaaa\U{0005}\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"aa\U{0003}aaaaaaaaZaaaaaaaa\U{0001}aaaa\U{0005}\U{0007}"| && ("aa\U{0003}aaaaaaaaZaaaaaaaa\U{0001}aaaa\U{0005}\U{0007}"[i] == 'z' || "aa\U{0003}aaaaaaaaZaaaaaaaa\U{0001}aaaa\U{0005}\U{0007}"[i] == 'Z');
}
method {:test} Test48() {
var r0 := ContainsZ("\U{000E}\0a\U{0002}a\U{0004}aaa\U{0008}aaaaaaaaaaaa\U{000C}a\na\U{0006}a");
expect r0 <==> exists i :: 0 <= i < |"\U{000E}\0a\U{0002}a\U{0004}aaa\U{0008}aaaaaaaaaaaa\U{000C}a\na\U{0006}a"| && ("\U{000E}\0a\U{0002}a\U{0004}aaa\U{0008}aaaaaaaaaaaa\U{000C}a\na\U{0006}a"[i] == 'z' || "\U{000E}\0a\U{0002}a\U{0004}aaa\U{0008}aaaaaaaaaaaa\U{000C}a\na\U{0006}a"[i] == 'Z');
}

// REPEAT 10 - TIME: 35.726637 s
