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


method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2)
    {
        if s[i] == '.' && |s| - i - 1 == 2 {
            result := true;
            break;
        }
    }
}

method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("");
expect r0 ==> exists i :: 0 <= i < |""| && ""[i] == '.' && |""| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |""| && ""[i] == '.' && |""| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 3.2681434 s

method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 4.664928 s

method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\0");
expect r0 ==> exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 6.1433315 s

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision(".\U{0001}\U{0003}");
expect r0 ==> exists i :: 0 <= i < |".\U{0001}\U{0003}"| && ".\U{0001}\U{0003}"[i] == '.' && |".\U{0001}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\U{0001}\U{0003}"| && ".\U{0001}\U{0003}"[i] == '.' && |".\U{0001}\U{0003}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 7.5535103 s

method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}a\0aaaaaaaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| && "\U{0004}a\0aaaaaaaaaaa\U{0002}"[i] == '.' && |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| && "\U{0004}a\0aaaaaaaaaaa\U{0002}"[i] == '.' && |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| && "aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| && "aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 8.7500792 s

method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("a\0\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"a\0\U{0004}\U{0002}"| && "a\0\U{0004}\U{0002}"[i] == '.' && |"a\0\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\0\U{0004}\U{0002}"| && "a\0\U{0004}\U{0002}"[i] == '.' && |"a\0\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaa.\U{0001}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaa.\U{0001}a"| && "\U{0003}aaaaa.\U{0001}a"[i] == '.' && |"\U{0003}aaaaa.\U{0001}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaa.\U{0001}a"| && "\U{0003}aaaaa.\U{0001}a"[i] == '.' && |"\U{0003}aaaaa.\U{0001}a"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 9.9280417 s

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a\0"| && "\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a\0"[i] == '.' && |"\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a\0"| && "\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a\0"[i] == '.' && |"\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a\0"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaa\U{0001}aaaaaaaaa\U{0005}\U{0007}aaaaaaaaaaaaaaaaaaaaaaaaa.\t\U{000B}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaa\U{0001}aaaaaaaaa\U{0005}\U{0007}aaaaaaaaaaaaaaaaaaaaaaaaa.\t\U{000B}"| && "\U{0003}aaa\U{0001}aaaaaaaaa\U{0005}\U{0007}aaaaaaaaaaaaaaaaaaaaaaaaa.\t\U{000B}"[i] == '.' && |"\U{0003}aaa\U{0001}aaaaaaaaa\U{0005}\U{0007}aaaaaaaaaaaaaaaaaaaaaaaaa.\t\U{000B}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaa\U{0001}aaaaaaaaa\U{0005}\U{0007}aaaaaaaaaaaaaaaaaaaaaaaaa.\t\U{000B}"| && "\U{0003}aaa\U{0001}aaaaaaaaa\U{0005}\U{0007}aaaaaaaaaaaaaaaaaaaaaaaaa.\t\U{000B}"[i] == '.' && |"\U{0003}aaa\U{0001}aaaaaaaaa\U{0005}\U{0007}aaaaaaaaaaaaaaaaaaaaaaaaa.\t\U{000B}"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 11.3107815 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && "\U{0004}\0\U{0002}"[i] == '.' && |"\U{0004}\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && "\U{0004}\0\U{0002}"[i] == '.' && |"\U{0004}\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}aa.\U{0001}\U{0003}");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}aa.\U{0001}\U{0003}"| && "\U{0005}aa.\U{0001}\U{0003}"[i] == '.' && |"\U{0005}aa.\U{0001}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}aa.\U{0001}\U{0003}"| && "\U{0005}aa.\U{0001}\U{0003}"[i] == '.' && |"\U{0005}aa.\U{0001}\U{0003}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 12.916601 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}a.\0a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}a.\0a"| && "\U{0002}a.\0a"[i] == '.' && |"\U{0002}a.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}a.\0a"| && "\U{0002}a.\0a"[i] == '.' && |"\U{0002}a.\0a"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 14.7012192 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}");
expect r0 ==> exists i :: 0 <= i < |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| && "\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"[i] == '.' && |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| && "\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"[i] == '.' && |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 15.7943757 s
