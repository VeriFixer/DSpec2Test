// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if |s| == 0 {
    result := false;
  } else {
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result <==> forall k :: 0 <= k < i ==> IsDigit(s[k])
    {
      if !IsDigit(s[i]) {
        break;
      }
    }
  }
}


method {:test} Test0() {
var r0 := IsInteger("aaaaaaaa/");
expect r0 <==> |"aaaaaaaa/"| > 0 && forall i :: 0 <= i < |"aaaaaaaa/"| ==> IsDigit("aaaaaaaa/"[i]);
}
method {:test} Test1() {
var r0 := IsInteger("");
expect r0 <==> |""| > 0 && forall i :: 0 <= i < |""| ==> IsDigit(""[i]);
}

// REPEAT 1 - TIME: 2.9452858 s

method {:test} Test2() {
var r0 := IsInteger("aaaaaa\U{0008}");
expect r0 <==> |"aaaaaa\U{0008}"| > 0 && forall i :: 0 <= i < |"aaaaaa\U{0008}"| ==> IsDigit("aaaaaa\U{0008}"[i]);
}
method {:test} Test3() {
var r0 := IsInteger("\U{0008}");
expect r0 <==> |"\U{0008}"| > 0 && forall i :: 0 <= i < |"\U{0008}"| ==> IsDigit("\U{0008}"[i]);
}

// REPEAT 2 - TIME: 4.071369 s

method {:test} Test4() {
var r0 := IsInteger("\t0");
expect r0 <==> |"\t0"| > 0 && forall i :: 0 <= i < |"\t0"| ==> IsDigit("\t0"[i]);
}
method {:test} Test5() {
var r0 := IsInteger("\taaaaaa\0");
expect r0 <==> |"\taaaaaa\0"| > 0 && forall i :: 0 <= i < |"\taaaaaa\0"| ==> IsDigit("\taaaaaa\0"[i]);
}

// REPEAT 3 - TIME: 5.1839332 s

method {:test} Test6() {
var r0 := IsInteger("\t\0\U{0002}");
expect r0 <==> |"\t\0\U{0002}"| > 0 && forall i :: 0 <= i < |"\t\0\U{0002}"| ==> IsDigit("\t\0\U{0002}"[i]);
}
method {:test} Test7() {
var r0 := IsInteger("\U{0007}\0\U{0001}");
expect r0 <==> |"\U{0007}\0\U{0001}"| > 0 && forall i :: 0 <= i < |"\U{0007}\0\U{0001}"| ==> IsDigit("\U{0007}\0\U{0001}"[i]);
}

// REPEAT 4 - TIME: 6.4598423 s

method {:test} Test8() {
var r0 := IsInteger("\U{0008}a\0a");
expect r0 <==> |"\U{0008}a\0a"| > 0 && forall i :: 0 <= i < |"\U{0008}a\0a"| ==> IsDigit("\U{0008}a\0a"[i]);
}
method {:test} Test9() {
var r0 := IsInteger("\n\0");
expect r0 <==> |"\n\0"| > 0 && forall i :: 0 <= i < |"\n\0"| ==> IsDigit("\n\0"[i]);
}

// REPEAT 5 - TIME: 8.0855908 s

method {:test} Test10() {
var r0 := IsInteger("\U{0008}aa\U{0001}\U{0003}");
expect r0 <==> |"\U{0008}aa\U{0001}\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0008}aa\U{0001}\U{0003}"| ==> IsDigit("\U{0008}aa\U{0001}\U{0003}"[i]);
}
method {:test} Test11() {
var r0 := IsInteger("\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}");
expect r0 <==> |"\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}"| > 0 && forall i :: 0 <= i < |"\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}"| ==> IsDigit("\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}"[i]);
}

// REPEAT 6 - TIME: 9.6493108 s

method {:test} Test12() {
var r0 := IsInteger("\U{0019}a\0\U{0003}");
expect r0 <==> |"\U{0019}a\0\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0019}a\0\U{0003}"| ==> IsDigit("\U{0019}a\0\U{0003}"[i]);
}
method {:test} Test13() {
var r0 := IsInteger("\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}");
expect r0 <==> |"\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}"| > 0 && forall i :: 0 <= i < |"\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}"| ==> IsDigit("\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}"[i]);
}

// REPEAT 7 - TIME: 10.8163967 s

method {:test} Test14() {
var r0 := IsInteger("\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}");
expect r0 <==> |"\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}"| > 0 && forall i :: 0 <= i < |"\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}"| ==> IsDigit("\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}"[i]);
}
method {:test} Test15() {
var r0 := IsInteger("\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}");
expect r0 <==> |"\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}"| > 0 && forall i :: 0 <= i < |"\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}"| ==> IsDigit("\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}"[i]);
}

// REPEAT 8 - TIME: 11.7070815 s

method {:test} Test16() {
var r0 := IsInteger("-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}");
expect r0 <==> |"-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}"| > 0 && forall i :: 0 <= i < |"-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}"| ==> IsDigit("-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}"[i]);
}
method {:test} Test17() {
var r0 := IsInteger("\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r");
expect r0 <==> |"\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r"| > 0 && forall i :: 0 <= i < |"\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r"| ==> IsDigit("\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r"[i]);
}

// REPEAT 9 - TIME: 12.8284846 s

method {:test} Test18() {
var r0 := IsInteger("2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}");
expect r0 <==> |"2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}"| > 0 && forall i :: 0 <= i < |"2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}"| ==> IsDigit("2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}"[i]);
}
method {:test} Test19() {
var r0 := IsInteger("\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}");
expect r0 <==> |"\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}"| > 0 && forall i :: 0 <= i < |"\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}"| ==> IsDigit("\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}"[i]);
}

// REPEAT 10 - TIME: 14.0078192 s
