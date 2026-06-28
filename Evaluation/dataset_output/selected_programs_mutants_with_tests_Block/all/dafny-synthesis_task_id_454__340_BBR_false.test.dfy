// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if false {
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

// REPEAT 1 - TIME: 2.8414615 s

method {:test} Test2() {
var r0 := ContainsZ("aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}"| && ("aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}"[i] == 'z' || "aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}"[i] == 'Z');
}
method {:test} Test3() {
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}

// REPEAT 2 - TIME: 4.0356094 s

method {:test} Test4() {
var r0 := ContainsZ("Z\0");
expect r0 <==> exists i :: 0 <= i < |"Z\0"| && ("Z\0"[i] == 'z' || "Z\0"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("a\0z");
expect r0 <==> exists i :: 0 <= i < |"a\0z"| && ("a\0z"[i] == 'z' || "a\0z"[i] == 'Z');
}

// REPEAT 3 - TIME: 5.4000117 s

method {:test} Test6() {
var r0 := ContainsZ("za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}"| && ("za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}"[i] == 'z' || "za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0002}aa\0aaaa\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aa\0aaaa\U{0004}\U{0006}"| && ("\U{0002}aa\0aaaa\U{0004}\U{0006}"[i] == 'z' || "\U{0002}aa\0aaaa\U{0004}\U{0006}"[i] == 'Z');
}

// REPEAT 4 - TIME: 6.8438237 s

method {:test} Test8() {
var r0 := ContainsZ("Za\U{0003}aaaaaaaaaaaaaa\U{0005}aaa\U{0001}\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"Za\U{0003}aaaaaaaaaaaaaa\U{0005}aaa\U{0001}\U{0007}"| && ("Za\U{0003}aaaaaaaaaaaaaa\U{0005}aaa\U{0001}\U{0007}"[i] == 'z' || "Za\U{0003}aaaaaaaaaaaaaa\U{0005}aaa\U{0001}\U{0007}"[i] == 'Z');
}
method {:test} Test9() {
var r0 := ContainsZ("a\U{0002}\0z");
expect r0 <==> exists i :: 0 <= i < |"a\U{0002}\0z"| && ("a\U{0002}\0z"[i] == 'z' || "a\U{0002}\0z"[i] == 'Z');
}

// REPEAT 5 - TIME: 8.5639992 s

method {:test} Test10() {
var r0 := ContainsZ("\U{0002}\0aa\U{0004}Zaaa\U{0006}\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0aa\U{0004}Zaaa\U{0006}\U{0008}"| && ("\U{0002}\0aa\U{0004}Zaaa\U{0006}\U{0008}"[i] == 'z' || "\U{0002}\0aa\U{0004}Zaaa\U{0006}\U{0008}"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}z"| && ("\U{0001}z"[i] == 'z' || "\U{0001}z"[i] == 'Z');
}

// REPEAT 6 - TIME: 10.0390928 s

method {:test} Test12() {
var r0 := ContainsZ("Z\U{0005}a\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"Z\U{0005}a\0\U{0002}"| && ("Z\U{0005}a\0\U{0002}"[i] == 'z' || "Z\U{0005}a\0\U{0002}"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\U{0004}a\U{0002}\0z");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\U{0002}\0z"| && ("\U{0004}a\U{0002}\0z"[i] == 'z' || "\U{0004}a\U{0002}\0z"[i] == 'Z');
}

// REPEAT 7 - TIME: 11.4457961 s

method {:test} Test14() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaa\U{0002}\0Z\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaa\U{0002}\0Z\U{0004}"| && ("aaaaaaaaaaaaaaaaaaaaa\U{0002}\0Z\U{0004}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaa\U{0002}\0Z\U{0004}"[i] == 'Z');
}
method {:test} Test15() {
var r0 := ContainsZ("\0\U{0002}azaa");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}azaa"| && ("\0\U{0002}azaa"[i] == 'z' || "\0\U{0002}azaa"[i] == 'Z');
}

// REPEAT 8 - TIME: 12.8834422 s

method {:test} Test16() {
var r0 := ContainsZ("\U{0004}aaaa\0a\U{0002}az");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}aaaa\0a\U{0002}az"| && ("\U{0004}aaaa\0a\U{0002}az"[i] == 'z' || "\U{0004}aaaa\0a\U{0002}az"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\0");
expect r0 <==> exists i :: 0 <= i < |"\0"| && ("\0"[i] == 'z' || "\0"[i] == 'Z');
}

// REPEAT 9 - TIME: 13.9990811 s

method {:test} Test18() {
var r0 := ContainsZ("aaaaaaaZaa\0aaaaaa\U{0002}aaaaa\U{0004}aa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaZaa\0aaaaaa\U{0002}aaaaa\U{0004}aa"| && ("aaaaaaaZaa\0aaaaaa\U{0002}aaaaa\U{0004}aa"[i] == 'z' || "aaaaaaaZaa\0aaaaaa\U{0002}aaaaa\U{0004}aa"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\0z");
expect r0 <==> exists i :: 0 <= i < |"\0z"| && ("\0z"[i] == 'z' || "\0z"[i] == 'Z');
}

// REPEAT 10 - TIME: 15.2411379 s
