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

// REPEAT 1 - TIME: 12.1779241 s

method {:test} Test22() {
var r0 := ContainsZ("\0aaaaaaaz\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\0aaaaaaaz\U{0003}"| && ("\0aaaaaaaz\U{0003}"[i] == 'z' || "\0aaaaaaaz\U{0003}"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\0aaaaaaaZ\U{0004}\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\0aaaaaaaZ\U{0004}\U{0002}"| && ("\0aaaaaaaZ\U{0004}\U{0002}"[i] == 'z' || "\0aaaaaaaZ\U{0004}\U{0002}"[i] == 'Z');
}
method {:test} Test24() {
var r0 := ContainsZ("\U{0006}\0\U{0002}aaaa\U{0004}a\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}\0\U{0002}aaaa\U{0004}a\U{0008}"| && ("\U{0006}\0\U{0002}aaaa\U{0004}a\U{0008}"[i] == 'z' || "\U{0006}\0\U{0002}aaaa\U{0004}a\U{0008}"[i] == 'Z');
}

// REPEAT 2 - TIME: 13.4446936 s

method {:test} Test25() {
var r0 := ContainsZ("\U{0002}\0z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0z"| && ("\U{0002}\0z"[i] == 'z' || "\U{0002}\0z"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("\U{0003}Zaa\U{0001}aaa\U{0005}\U{0007}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}Zaa\U{0001}aaa\U{0005}\U{0007}a"| && ("\U{0003}Zaa\U{0001}aaa\U{0005}\U{0007}a"[i] == 'z' || "\U{0003}Zaa\U{0001}aaa\U{0005}\U{0007}a"[i] == 'Z');
}
method {:test} Test27() {
var r0 := ContainsZ("\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0"| && ("\U{0002}\0"[i] == 'z' || "\U{0002}\0"[i] == 'Z');
}

// REPEAT 3 - TIME: 14.9684936 s

method {:test} Test28() {
var r0 := ContainsZ("\U{0006}az\0a\U{0004}aaa\U{0008}\n\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}az\0a\U{0004}aaa\U{0008}\n\U{0002}"| && ("\U{0006}az\0a\U{0004}aaa\U{0008}\n\U{0002}"[i] == 'z' || "\U{0006}az\0a\U{0004}aaa\U{0008}\n\U{0002}"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("\U{0002}aZ\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aZ\0"| && ("\U{0002}aZ\0"[i] == 'z' || "\U{0002}aZ\0"[i] == 'Z');
}
method {:test} Test30() {
var r0 := ContainsZ("\U{0002}a\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0"| && ("\U{0002}a\0"[i] == 'z' || "\U{0002}a\0"[i] == 'Z');
}

// REPEAT 4 - TIME: 16.4220947 s

method {:test} Test31() {
var r0 := ContainsZ("\U{0001}az");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}az"| && ("\U{0001}az"[i] == 'z' || "\U{0001}az"[i] == 'Z');
}
method {:test} Test32() {
var r0 := ContainsZ("\U{0005}a\U{0001}aaa\U{0003}\U{0007}Z\t");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}a\U{0001}aaa\U{0003}\U{0007}Z\t"| && ("\U{0005}a\U{0001}aaa\U{0003}\U{0007}Z\t"[i] == 'z' || "\U{0005}a\U{0001}aaa\U{0003}\U{0007}Z\t"[i] == 'Z');
}
method {:test} Test33() {
var r0 := ContainsZ("\U{0008}\U{0002}\0\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}\U{0002}\0\U{0004}\U{0006}"| && ("\U{0008}\U{0002}\0\U{0004}\U{0006}"[i] == 'z' || "\U{0008}\U{0002}\0\U{0004}\U{0006}"[i] == 'Z');
}

// REPEAT 5 - TIME: 17.9974089 s

method {:test} Test34() {
var r0 := ContainsZ("\U{0003}az\U{0001}a\U{0005}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}az\U{0001}a\U{0005}"| && ("\U{0003}az\U{0001}a\U{0005}"[i] == 'z' || "\U{0003}az\U{0001}a\U{0005}"[i] == 'Z');
}
method {:test} Test35() {
var r0 := ContainsZ("\U{000B}aZ\U{0007}a\U{0003}aaa\U{0005}\U{0001}\t");
expect r0 <==> exists i :: 0 <= i < |"\U{000B}aZ\U{0007}a\U{0003}aaa\U{0005}\U{0001}\t"| && ("\U{000B}aZ\U{0007}a\U{0003}aaa\U{0005}\U{0001}\t"[i] == 'z' || "\U{000B}aZ\U{0007}a\U{0003}aaa\U{0005}\U{0001}\t"[i] == 'Z');
}
method {:test} Test36() {
var r0 := ContainsZ("aa\U{0002}aaa\U{0008}a\0a\n\U{0006}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"aa\U{0002}aaa\U{0008}a\0a\n\U{0006}\U{0004}"| && ("aa\U{0002}aaa\U{0008}a\0a\n\U{0006}\U{0004}"[i] == 'z' || "aa\U{0002}aaa\U{0008}a\0a\n\U{0006}\U{0004}"[i] == 'Z');
}

// REPEAT 6 - TIME: 19.3011226 s

method {:test} Test37() {
var r0 := ContainsZ("\U{0005}a\U{0003}aaaa\U{0001}aaz\U{0007}\U{000B}\t");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}a\U{0003}aaaa\U{0001}aaz\U{0007}\U{000B}\t"| && ("\U{0005}a\U{0003}aaaa\U{0001}aaz\U{0007}\U{000B}\t"[i] == 'z' || "\U{0005}a\U{0003}aaaa\U{0001}aaz\U{0007}\U{000B}\t"[i] == 'Z');
}
method {:test} Test38() {
var r0 := ContainsZ("\U{000B}aZaa\U{0005}a\U{0001}a\U{0007}\U{0003}\t");
expect r0 <==> exists i :: 0 <= i < |"\U{000B}aZaa\U{0005}a\U{0001}a\U{0007}\U{0003}\t"| && ("\U{000B}aZaa\U{0005}a\U{0001}a\U{0007}\U{0003}\t"[i] == 'z' || "\U{000B}aZaa\U{0005}a\U{0001}a\U{0007}\U{0003}\t"[i] == 'Z');
}
method {:test} Test39() {
var r0 := ContainsZ("\U{0012}\0a\U{0002}\na\U{0004}\U{0008}\U{000C}\U{000E}\U{0006}\U{0010}");
expect r0 <==> exists i :: 0 <= i < |"\U{0012}\0a\U{0002}\na\U{0004}\U{0008}\U{000C}\U{000E}\U{0006}\U{0010}"| && ("\U{0012}\0a\U{0002}\na\U{0004}\U{0008}\U{000C}\U{000E}\U{0006}\U{0010}"[i] == 'z' || "\U{0012}\0a\U{0002}\na\U{0004}\U{0008}\U{000C}\U{000E}\U{0006}\U{0010}"[i] == 'Z');
}

// REPEAT 7 - TIME: 20.4699344 s

method {:test} Test40() {
var r0 := ContainsZ("\U{0005}a\U{0001}aaaaaz\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}a\U{0001}aaaaaz\U{0003}"| && ("\U{0005}a\U{0001}aaaaaz\U{0003}"[i] == 'z' || "\U{0005}a\U{0001}aaaaaz\U{0003}"[i] == 'Z');
}
method {:test} Test41() {
var r0 := ContainsZ("\raa\U{0003}aa\U{0001}aZa\U{0005}\U{0007}\t\U{000B}a");
expect r0 <==> exists i :: 0 <= i < |"\raa\U{0003}aa\U{0001}aZa\U{0005}\U{0007}\t\U{000B}a"| && ("\raa\U{0003}aa\U{0001}aZa\U{0005}\U{0007}\t\U{000B}a"[i] == 'z' || "\raa\U{0003}aa\U{0001}aZa\U{0005}\U{0007}\t\U{000B}a"[i] == 'Z');
}
method {:test} Test42() {
var r0 := ContainsZ("\n\U{0004}\U{0008}aaa\0aa\U{0002}\U{0006}\U{000C}a");
expect r0 <==> exists i :: 0 <= i < |"\n\U{0004}\U{0008}aaa\0aa\U{0002}\U{0006}\U{000C}a"| && ("\n\U{0004}\U{0008}aaa\0aa\U{0002}\U{0006}\U{000C}a"[i] == 'z' || "\n\U{0004}\U{0008}aaa\0aa\U{0002}\U{0006}\U{000C}a"[i] == 'Z');
}

// REPEAT 8 - TIME: 21.7994002 s

method {:test} Test43() {
var r0 := ContainsZ("\U{0003}a\U{0001}z\U{0005}\t\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}a\U{0001}z\U{0005}\t\U{0007}"| && ("\U{0003}a\U{0001}z\U{0005}\t\U{0007}"[i] == 'z' || "\U{0003}a\U{0001}z\U{0005}\t\U{0007}"[i] == 'Z');
}
method {:test} Test44() {
var r0 := ContainsZ("\U{0003}aaa\U{0005}aZaa\U{0001}\t\U{000B}a\U{0007}\U{000F}\r");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaa\U{0005}aZaa\U{0001}\t\U{000B}a\U{0007}\U{000F}\r"| && ("\U{0003}aaa\U{0005}aZaa\U{0001}\t\U{000B}a\U{0007}\U{000F}\r"[i] == 'z' || "\U{0003}aaa\U{0005}aZaa\U{0001}\t\U{000B}a\U{0007}\U{000F}\r"[i] == 'Z');
}
method {:test} Test45() {
var r0 := ContainsZ("\U{0006}aaaaa\0a\U{0004}\n\U{0002}a\U{000C}a\U{0008}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aaaaa\0a\U{0004}\n\U{0002}a\U{000C}a\U{0008}a"| && ("\U{0006}aaaaa\0a\U{0004}\n\U{0002}a\U{000C}a\U{0008}a"[i] == 'z' || "\U{0006}aaaaa\0a\U{0004}\n\U{0002}a\U{000C}a\U{0008}a"[i] == 'Z');
}

// REPEAT 9 - TIME: 23.1886908 s

method {:test} Test46() {
var r0 := ContainsZ("aaaaz\U{0001}a\U{0003}aaa\U{0007}\taa\U{000B}\U{0005}");
expect r0 <==> exists i :: 0 <= i < |"aaaaz\U{0001}a\U{0003}aaa\U{0007}\taa\U{000B}\U{0005}"| && ("aaaaz\U{0001}a\U{0003}aaa\U{0007}\taa\U{000B}\U{0005}"[i] == 'z' || "aaaaz\U{0001}a\U{0003}aaa\U{0007}\taa\U{000B}\U{0005}"[i] == 'Z');
}
method {:test} Test47() {
var r0 := ContainsZ("aaaaZ\U{0003}\U{0005}a\ta\U{0007}a\U{0001}a\ra\U{000B}");
expect r0 <==> exists i :: 0 <= i < |"aaaaZ\U{0003}\U{0005}a\ta\U{0007}a\U{0001}a\ra\U{000B}"| && ("aaaaZ\U{0003}\U{0005}a\ta\U{0007}a\U{0001}a\ra\U{000B}"[i] == 'z' || "aaaaZ\U{0003}\U{0005}a\ta\U{0007}a\U{0001}a\ra\U{000B}"[i] == 'Z');
}
method {:test} Test48() {
var r0 := ContainsZ("\U{0002}aaaaaaaa\U{0004}a\0\U{0008}a\U{0006}\U{000C}\n");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}a\0\U{0008}a\U{0006}\U{000C}\n"| && ("\U{0002}aaaaaaaa\U{0004}a\0\U{0008}a\U{0006}\U{000C}\n"[i] == 'z' || "\U{0002}aaaaaaaa\U{0004}a\0\U{0008}a\U{0006}\U{000C}\n"[i] == 'Z');
}

// REPEAT 10 - TIME: 24.7314664 s
