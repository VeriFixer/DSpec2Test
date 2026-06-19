// dafny-synthesis_task_id_759.dfy

method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  ensures result ==> exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  ensures !result ==> !exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
  {
    if s[i] != '.' && |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("a");
expect r0 ==> exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 28.0714434 s

method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("a\0");
expect r0 ==> exists i :: 0 <= i < |"a\0"| && "a\0"[i] == '.' && |"a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\0"| && "a\0"[i] == '.' && |"a\0"| - i - 1 == 2;
}
method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaa.aa"| && "\U{0001}aaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaa.aa"| && "\U{0001}aaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 54.8689201 s

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaa.\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaa.\0\U{0002}"| && "aaaaaaaaaaaaaaa.\0\U{0002}"[i] == '.' && |"aaaaaaaaaaaaaaa.\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaa.\0\U{0002}"| && "aaaaaaaaaaaaaaa.\0\U{0002}"[i] == '.' && |"aaaaaaaaaaaaaaa.\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("aa\0aaaaaaaaaa.\U{0002}a");
expect r0 ==> exists i :: 0 <= i < |"aa\0aaaaaaaaaa.\U{0002}a"| && "aa\0aaaaaaaaaa.\U{0002}a"[i] == '.' && |"aa\0aaaaaaaaaa.\U{0002}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\0aaaaaaaaaa.\U{0002}a"| && "aa\0aaaaaaaaaa.\U{0002}a"[i] == '.' && |"aa\0aaaaaaaaaa.\U{0002}a"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 85.412012 s

method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0a"| && "\U{0002}\0a"[i] == '.' && |"\U{0002}\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0a"| && "\U{0002}\0a"[i] == '.' && |"\U{0002}\0a"| - i - 1 == 2;
}
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaa\U{0004}.\U{0002}a");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0004}.\U{0002}a"| && "\0aaaaaaaaaaaa\U{0004}.\U{0002}a"[i] == '.' && |"\0aaaaaaaaaaaa\U{0004}.\U{0002}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0004}.\U{0002}a"| && "\0aaaaaaaaaaaa\U{0004}.\U{0002}a"[i] == '.' && |"\0aaaaaaaaaaaa\U{0004}.\U{0002}a"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaa.\0\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaa.\0\U{0004}"| && "\U{0002}aaaaaaaaaaaaaaa.\0\U{0004}"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaa.\0\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaa.\0\U{0004}"| && "\U{0002}aaaaaaaaaaaaaaa.\0\U{0004}"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaa.\0\U{0004}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 124.0101416 s

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| && "\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| && "\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| && "aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"[i] == '.' && |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| && "aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"[i] == '.' && |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 170.8094582 s

method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\0aa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0aa\U{0002}"| && "\0aa\U{0002}"[i] == '.' && |"\0aa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aa\U{0002}"| && "\0aa\U{0002}"[i] == '.' && |"\0aa\U{0002}"| - i - 1 == 2;
}
method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa.\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa.\0\U{0002}"| && "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa.\0\U{0002}"[i] == '.' && |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa.\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa.\0\U{0002}"| && "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa.\0\U{0002}"[i] == '.' && |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa.\0\U{0002}"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 238.131123 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\0a");
expect r0 ==> exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0007}aaaaaaaaaaaaaaaaaa\U{0003}.\U{0005}\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaaaaa\U{0003}.\U{0005}\U{0001}"| && "\U{0007}aaaaaaaaaaaaaaaaaa\U{0003}.\U{0005}\U{0001}"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaaaaa\U{0003}.\U{0005}\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaaaaa\U{0003}.\U{0005}\U{0001}"| && "\U{0007}aaaaaaaaaaaaaaaaaa\U{0003}.\U{0005}\U{0001}"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaaaaa\U{0003}.\U{0005}\U{0001}"| - i - 1 == 2;
}
method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}aaaaaaaaaaaaaaaaaa\U{0001}.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}aaaaaaaaaaaaaaaaaa\U{0001}.\U{0003}a"| && "\U{0005}aaaaaaaaaaaaaaaaaa\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}aaaaaaaaaaaaaaaaaa\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}aaaaaaaaaaaaaaaaaa\U{0001}.\U{0003}a"| && "\U{0005}aaaaaaaaaaaaaaaaaa\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}aaaaaaaaaaaaaaaaaa\U{0001}.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 280.8981117 s

method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}\U{0004}a\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}\U{0004}a\U{0002}\0"| && "\U{0006}\U{0004}a\U{0002}\0"[i] == '.' && |"\U{0006}\U{0004}a\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}\U{0004}a\U{0002}\0"| && "\U{0006}\U{0004}a\U{0002}\0"[i] == '.' && |"\U{0006}\U{0004}a\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| && "aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| && "aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 357.9902958 s

method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 411.3255688 s

method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaa\0a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaa\0a"| && "\U{0002}aaa\0a"[i] == '.' && |"\U{0002}aaa\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaa\0a"| && "\U{0002}aaa\0a"[i] == '.' && |"\U{0002}aaa\0a"| - i - 1 == 2;
}
method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 473.3470007 s
