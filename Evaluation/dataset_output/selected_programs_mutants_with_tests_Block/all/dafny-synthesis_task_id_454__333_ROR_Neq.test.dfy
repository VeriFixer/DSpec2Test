// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] != 'z' || s[i] == 'Z' {
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
var r0 := ContainsZ("aaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaZ"| && ("aaaaaaaaZ"[i] == 'z' || "aaaaaaaaZ"[i] == 'Z');
}
method {:test} Test1() {
var r0 := ContainsZ("aaaaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaz"| && ("aaaaaaaz"[i] == 'z' || "aaaaaaaz"[i] == 'Z');
}

// REPEAT 1 - TIME: 3.4204972 s

method {:test} Test2() {
var r0 := ContainsZ("\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}Z"| && ("\U{0001}Z"[i] == 'z' || "\U{0001}Z"[i] == 'Z');
}
method {:test} Test3() {
var r0 := ContainsZ("a\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"a\U{0001}z"| && ("a\U{0001}z"[i] == 'z' || "a\U{0001}z"[i] == 'Z');
}

// REPEAT 2 - TIME: 5.0211322 s

method {:test} Test4() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("\U{0002}a\0z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0z"| && ("\U{0002}a\0z"[i] == 'z' || "\U{0002}a\0z"[i] == 'Z');
}

// REPEAT 3 - TIME: 6.5918238 s

method {:test} Test6() {
var r0 := ContainsZ("za\0\U{0002}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"za\0\U{0002}\U{0004}"| && ("za\0\U{0002}\U{0004}"[i] == 'z' || "za\0\U{0002}\U{0004}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\0a\U{0002}\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\0a\U{0002}\U{0004}\U{0006}"| && ("\0a\U{0002}\U{0004}\U{0006}"[i] == 'z' || "\0a\U{0002}\U{0004}\U{0006}"[i] == 'Z');
}

// REPEAT 4 - TIME: 7.799926 s

method {:test} Test8() {
var r0 := ContainsZ("\0Z");
expect r0 <==> exists i :: 0 <= i < |"\0Z"| && ("\0Z"[i] == 'z' || "\0Z"[i] == 'Z');
}
method {:test} Test9() {
var r0 := ContainsZ("\U{0002}\0za");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0za"| && ("\U{0002}\0za"[i] == 'z' || "\U{0002}\0za"[i] == 'Z');
}

// REPEAT 5 - TIME: 9.0002711 s

method {:test} Test10() {
var r0 := ContainsZ("\0Z");
expect r0 <==> exists i :: 0 <= i < |"\0Z"| && ("\0Z"[i] == 'z' || "\0Z"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\U{0004}\U{0002}\0zaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\U{0002}\0zaaa"| && ("\U{0004}\U{0002}\0zaaa"[i] == 'z' || "\U{0004}\U{0002}\0zaaa"[i] == 'Z');
}

// REPEAT 6 - TIME: 10.125363 s

method {:test} Test12() {
var r0 := ContainsZ("\0Za\U{0002}\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\0Za\U{0002}\U{0004}\U{0006}"| && ("\0Za\U{0002}\U{0004}\U{0006}"[i] == 'z' || "\0Za\U{0002}\U{0004}\U{0006}"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\U{0002}z\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}z\0"| && ("\U{0002}z\0"[i] == 'z' || "\U{0002}z\0"[i] == 'Z');
}

// REPEAT 7 - TIME: 11.4212722 s

method {:test} Test14() {
var r0 := ContainsZ("\0aa\U{0004}a\na\U{0006}\U{0008}\U{0002}a\U{000C}aaaaaaaaa\U{000E}aaZ\U{0010}");
expect r0 <==> exists i :: 0 <= i < |"\0aa\U{0004}a\na\U{0006}\U{0008}\U{0002}a\U{000C}aaaaaaaaa\U{000E}aaZ\U{0010}"| && ("\0aa\U{0004}a\na\U{0006}\U{0008}\U{0002}a\U{000C}aaaaaaaaa\U{000E}aaZ\U{0010}"[i] == 'z' || "\0aa\U{0004}a\na\U{0006}\U{0008}\U{0002}a\U{000C}aaaaaaaaa\U{000E}aaZ\U{0010}"[i] == 'Z');
}
method {:test} Test15() {
var r0 := ContainsZ("\0z");
expect r0 <==> exists i :: 0 <= i < |"\0z"| && ("\0z"[i] == 'z' || "\0z"[i] == 'Z');
}

// REPEAT 8 - TIME: 12.558756 s

method {:test} Test16() {
var r0 := ContainsZ("Za\U{0001}\U{0007}\t\U{000B}a\r\U{0003}\U{0005}");
expect r0 <==> exists i :: 0 <= i < |"Za\U{0001}\U{0007}\t\U{000B}a\r\U{0003}\U{0005}"| && ("Za\U{0001}\U{0007}\t\U{000B}a\r\U{0003}\U{0005}"[i] == 'z' || "Za\U{0001}\U{0007}\t\U{000B}a\r\U{0003}\U{0005}"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0002}aa\U{0006}aaa\0aaaaaaaaaaaaa\U{0004}\U{0008}aaz\n");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aa\U{0006}aaa\0aaaaaaaaaaaaa\U{0004}\U{0008}aaz\n"| && ("\U{0002}aa\U{0006}aaa\0aaaaaaaaaaaaa\U{0004}\U{0008}aaz\n"[i] == 'z' || "\U{0002}aa\U{0006}aaa\0aaaaaaaaaaaaa\U{0004}\U{0008}aaz\n"[i] == 'Z');
}

// REPEAT 9 - TIME: 13.8265048 s

method {:test} Test18() {
var r0 := ContainsZ("zaaaa\0a\U{0002}\U{0006}\U{0004}\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"zaaaa\0a\U{0002}\U{0006}\U{0004}\U{0008}"| && ("zaaaa\0a\U{0002}\U{0006}\U{0004}\U{0008}"[i] == 'z' || "zaaaa\0a\U{0002}\U{0006}\U{0004}\U{0008}"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{0006}\0\U{0002}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}\0\U{0002}\U{0004}"| && ("\U{0006}\0\U{0002}\U{0004}"[i] == 'z' || "\U{0006}\0\U{0002}\U{0004}"[i] == 'Z');
}

// REPEAT 10 - TIME: 14.9912282 s
