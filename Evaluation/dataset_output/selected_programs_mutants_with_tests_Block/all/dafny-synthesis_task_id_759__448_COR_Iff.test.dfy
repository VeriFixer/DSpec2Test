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
    if s[i] == '.' <==> |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaa\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaa\0"| && "aaaaaaaa\0"[i] == '.' && |"aaaaaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaa\0"| && "aaaaaaaa\0"[i] == '.' && |"aaaaaaaa\0"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 3.5618569 s

method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("\0.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\0.\U{0003}a"| && "\0.\U{0003}a"[i] == '.' && |"\0.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0.\U{0003}a"| && "\0.\U{0003}a"[i] == '.' && |"\0.\U{0003}a"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaa\U{0002}a\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaa\U{0002}a\0"| && "aaaaaaaa\U{0002}a\0"[i] == '.' && |"aaaaaaaa\U{0002}a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaa\U{0002}a\0"| && "aaaaaaaa\U{0002}a\0"[i] == '.' && |"aaaaaaaa\U{0002}a\0"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 5.2533776 s

method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\0.aa");
expect r0 ==> exists i :: 0 <= i < |"\0.aa"| && "\0.aa"[i] == '.' && |"\0.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0.aa"| && "\0.aa"[i] == '.' && |"\0.aa"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("a\U{0002}\U{0004}a\0");
expect r0 ==> exists i :: 0 <= i < |"a\U{0002}\U{0004}a\0"| && "a\U{0002}\U{0004}a\0"[i] == '.' && |"a\U{0002}\U{0004}a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\U{0002}\U{0004}a\0"| && "a\U{0002}\U{0004}a\0"[i] == '.' && |"a\U{0002}\U{0004}a\0"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 6.5731445 s

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision(".\0a");
expect r0 ==> exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaa\0aaaa\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaa\0aaaa\U{0004}"| && "\U{0002}aaaaaaaaa\0aaaa\U{0004}"[i] == '.' && |"\U{0002}aaaaaaaaa\0aaaa\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaa\0aaaa\U{0004}"| && "\U{0002}aaaaaaaaa\0aaaa\U{0004}"[i] == '.' && |"\U{0002}aaaaaaaaa\0aaaa\U{0004}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 7.8725605 s

method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaaa\U{0002}.a\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaaa\U{0002}.a\0"| && "\U{0004}aaaaa\U{0002}.a\0"[i] == '.' && |"\U{0004}aaaaa\U{0002}.a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaaa\U{0002}.a\0"| && "\U{0004}aaaaa\U{0002}.a\0"[i] == '.' && |"\U{0004}aaaaa\U{0002}.a\0"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\0");
expect r0 ==> exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 9.0398612 s

method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}\U{0004}a\0a.a\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}\U{0004}a\0a.a\U{0002}"| && "\U{0006}\U{0004}a\0a.a\U{0002}"[i] == '.' && |"\U{0006}\U{0004}a\0a.a\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}\U{0004}a\0a.a\U{0002}"| && "\U{0006}\U{0004}a\0a.a\U{0002}"[i] == '.' && |"\U{0006}\U{0004}a\0a.a\U{0002}"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\0a");
expect r0 ==> exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 10.2564416 s

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aa.\U{0002}\0"| && "\U{0004}aa.\U{0002}\0"[i] == '.' && |"\U{0004}aa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aa.\U{0002}\0"| && "\U{0004}aa.\U{0002}\0"[i] == '.' && |"\U{0004}aa.\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\U{0004}\0a\U{0006}aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\U{0004}\0a\U{0006}aa"| && "\U{0002}\U{0004}\0a\U{0006}aa"[i] == '.' && |"\U{0002}\U{0004}\0a\U{0006}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\U{0004}\0a\U{0006}aa"| && "\U{0002}\U{0004}\0a\U{0006}aa"[i] == '.' && |"\U{0002}\U{0004}\0a\U{0006}aa"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 11.292394 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| && "\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"[i] == '.' && |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| && "\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"[i] == '.' && |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\0a\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0a\U{0002}"| && "\0a\U{0002}"[i] == '.' && |"\0a\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a\U{0002}"| && "\0a\U{0002}"[i] == '.' && |"\0a\U{0002}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 12.6007549 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0aaa\U{0004}aaaa\U{0006}aa\U{0008}a.\na");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0aaa\U{0004}aaaa\U{0006}aa\U{0008}a.\na"| && "\U{0002}\0aaa\U{0004}aaaa\U{0006}aa\U{0008}a.\na"[i] == '.' && |"\U{0002}\0aaa\U{0004}aaaa\U{0006}aa\U{0008}a.\na"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0aaa\U{0004}aaaa\U{0006}aa\U{0008}a.\na"| && "\U{0002}\0aaa\U{0004}aaaa\U{0006}aa\U{0008}a.\na"[i] == '.' && |"\U{0002}\0aaa\U{0004}aaaa\U{0006}aa\U{0008}a.\na"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\0\U{0002}\U{0004}aa");
expect r0 ==> exists i :: 0 <= i < |"\0\U{0002}\U{0004}aa"| && "\0\U{0002}\U{0004}aa"[i] == '.' && |"\0\U{0002}\U{0004}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0\U{0002}\U{0004}aa"| && "\0\U{0002}\U{0004}aa"[i] == '.' && |"\0\U{0002}\U{0004}aa"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 13.9930101 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n");
expect r0 ==> exists i :: 0 <= i < |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| && "a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"[i] == '.' && |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| && "a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"[i] == '.' && |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| && "\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| && "\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 15.3584054 s
