// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if true {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var r0 := ContainsZ("a");
expect r0 <==> exists i :: 0 <= i < |"a"| && ("a"[i] == 'z' || "a"[i] == 'Z');
}
method {:test} Test1() {
var r0 := ContainsZ("aaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaZ"| && ("aaaaaaaaZ"[i] == 'z' || "aaaaaaaaZ"[i] == 'Z');
}

// REPEAT 1 - TIME: 31.5319385 s

method {:test} Test3() {
var r0 := ContainsZ("\0a");
expect r0 <==> exists i :: 0 <= i < |"\0a"| && ("\0a"[i] == 'z' || "\0a"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("Z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Z\U{0001}"| && ("Z\U{0001}"[i] == 'z' || "Z\U{0001}"[i] == 'Z');
}

// REPEAT 2 - TIME: 68.1123105 s

method {:test} Test6() {
var r0 := ContainsZ("\0aa");
expect r0 <==> exists i :: 0 <= i < |"\0aa"| && ("\0aa"[i] == 'z' || "\0aa"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}"| && ("\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}"[i] == 'z' || "\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}"[i] == 'Z');
}

// REPEAT 3 - TIME: 111.0073601 s

method {:test} Test9() {
var r0 := ContainsZ("\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}"| && ("\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}"[i] == 'z' || "\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("Zaaaaaaaa\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"Zaaaaaaaa\0\U{0002}"| && ("Zaaaaaaaa\0\U{0002}"[i] == 'z' || "Zaaaaaaaa\0\U{0002}"[i] == 'Z');
}

// REPEAT 4 - TIME: 164.8508316 s

method {:test} Test12() {
var r0 := ContainsZ("\U{0004}a\0aaaa\U{0002}a\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0aaaa\U{0002}a\U{0006}"| && ("\U{0004}a\0aaaa\U{0002}a\U{0006}"[i] == 'z' || "\U{0004}a\0aaaa\U{0002}a\U{0006}"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("Zaa\0aaaaa\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"Zaa\0aaaaa\U{0002}"| && ("Zaa\0aaaaa\U{0002}"[i] == 'z' || "Zaa\0aaaaa\U{0002}"[i] == 'Z');
}

// REPEAT 5 - TIME: 228.5444939 s

method {:test} Test15() {
var r0 := ContainsZ("\U{0004}\0aaaaa\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0aaaaa\U{0002}"| && ("\U{0004}\0aaaaa\U{0002}"[i] == 'z' || "\U{0004}\0aaaaa\U{0002}"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z");
expect r0 <==> exists i :: 0 <= i < |"aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z"| && ("aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z"[i] == 'z' || "aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z"[i] == 'Z');
}

// REPEAT 6 - TIME: 289.193226 s

method {:test} Test18() {
var r0 := ContainsZ("\U{0006}aaaaaaa\U{0002}\0\U{0004}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aaaaaaa\U{0002}\0\U{0004}a"| && ("\U{0006}aaaaaaa\U{0002}\0\U{0004}a"[i] == 'z' || "\U{0006}aaaaaaa\U{0002}\0\U{0004}a"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa");
expect r0 <==> exists i :: 0 <= i < |"Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa"| && ("Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa"[i] == 'z' || "Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}"| && ("Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}"[i] == 'z' || "Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}"[i] == 'Z');
}

// REPEAT 7 - TIME: 383.1099626 s

method {:test} Test21() {
var r0 := ContainsZ("\U{0004}a\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0\U{0002}"| && ("\U{0004}a\0\U{0002}"[i] == 'z' || "\U{0004}a\0\U{0002}"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}"| && ("aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}"[i] == 'z' || "aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}"[i] == 'Z');
}

// REPEAT 8 - TIME: 484.3537131 s

method {:test} Test24() {
var r0 := ContainsZ("\U{0004}\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && ("\U{0004}\0\U{0002}"[i] == 'z' || "\U{0004}\0\U{0002}"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("aaZaaaaaaaaaaaaaa\0aaa");
expect r0 <==> exists i :: 0 <= i < |"aaZaaaaaaaaaaaaaa\0aaa"| && ("aaZaaaaaaaaaaaaaa\0aaa"[i] == 'z' || "aaZaaaaaaaaaaaaaa\0aaa"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("aZaaa");
expect r0 <==> exists i :: 0 <= i < |"aZaaa"| && ("aZaaa"[i] == 'z' || "aZaaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 632.0740673 s

method {:test} Test27() {
var r0 := ContainsZ("\U{0002}a\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0"| && ("\U{0002}a\0"[i] == 'z' || "\U{0002}a\0"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}

// REPEAT 10 - TIME: 846.6362174 s
