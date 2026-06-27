// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if |s| > 0 {
    result := false;
  } else {
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result <==> forall k :: 0 <= k < i ==> IsDigit(s[k])
    {
      if !IsDigit(s[i]) {
        result := false;
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

// REPEAT 1 - TIME: 2.644552 s

method {:test} Test2() {
var r0 := IsInteger("aaaaaa\U{0008}");
expect r0 <==> |"aaaaaa\U{0008}"| > 0 && forall i :: 0 <= i < |"aaaaaa\U{0008}"| ==> IsDigit("aaaaaa\U{0008}"[i]);
}
method {:test} Test3() {
var r0 := IsInteger("\U{0008}");
expect r0 <==> |"\U{0008}"| > 0 && forall i :: 0 <= i < |"\U{0008}"| ==> IsDigit("\U{0008}"[i]);
}

// REPEAT 2 - TIME: 4.0205401 s

method {:test} Test4() {
var r0 := IsInteger("\t\0");
expect r0 <==> |"\t\0"| > 0 && forall i :: 0 <= i < |"\t\0"| ==> IsDigit("\t\0"[i]);
}
method {:test} Test5() {
var r0 := IsInteger("\U{0008}\0aaaaaaaaaaaaaa\U{0001}");
expect r0 <==> |"\U{0008}\0aaaaaaaaaaaaaa\U{0001}"| > 0 && forall i :: 0 <= i < |"\U{0008}\0aaaaaaaaaaaaaa\U{0001}"| ==> IsDigit("\U{0008}\0aaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 5.2529837 s

method {:test} Test6() {
var r0 := IsInteger("\U{0007}a\0");
expect r0 <==> |"\U{0007}a\0"| > 0 && forall i :: 0 <= i < |"\U{0007}a\0"| ==> IsDigit("\U{0007}a\0"[i]);
}
method {:test} Test7() {
var r0 := IsInteger("\taa");
expect r0 <==> |"\taa"| > 0 && forall i :: 0 <= i < |"\taa"| ==> IsDigit("\taa"[i]);
}

// REPEAT 4 - TIME: 6.741605 s

method {:test} Test8() {
var r0 := IsInteger("\ta\0\U{0002}aa\U{0004}\U{0006}");
expect r0 <==> |"\ta\0\U{0002}aa\U{0004}\U{0006}"| > 0 && forall i :: 0 <= i < |"\ta\0\U{0002}aa\U{0004}\U{0006}"| ==> IsDigit("\ta\0\U{0002}aa\U{0004}\U{0006}"[i]);
}
method {:test} Test9() {
var r0 := IsInteger("\U{0019}a\0\U{0001}aaaaa\U{0002}");
expect r0 <==> |"\U{0019}a\0\U{0001}aaaaa\U{0002}"| > 0 && forall i :: 0 <= i < |"\U{0019}a\0\U{0001}aaaaa\U{0002}"| ==> IsDigit("\U{0019}a\0\U{0001}aaaaa\U{0002}"[i]);
}

// REPEAT 5 - TIME: 7.9753463 s

method {:test} Test10() {
var r0 := IsInteger("\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}");
expect r0 <==> |"\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}"| > 0 && forall i :: 0 <= i < |"\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}"| ==> IsDigit("\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}"[i]);
}
method {:test} Test11() {
var r0 := IsInteger("4\U{0019}a4");
expect r0 <==> |"4\U{0019}a4"| > 0 && forall i :: 0 <= i < |"4\U{0019}a4"| ==> IsDigit("4\U{0019}a4"[i]);
}

// REPEAT 6 - TIME: 9.5548049 s

method {:test} Test12() {
var r0 := IsInteger("\U{0007}a");
expect r0 <==> |"\U{0007}a"| > 0 && forall i :: 0 <= i < |"\U{0007}a"| ==> IsDigit("\U{0007}a"[i]);
}
method {:test} Test13() {
var r0 := IsInteger("%a\0aa");
expect r0 <==> |"%a\0aa"| > 0 && forall i :: 0 <= i < |"%a\0aa"| ==> IsDigit("%a\0aa"[i]);
}

// REPEAT 7 - TIME: 10.4528825 s

method {:test} Test14() {
var r0 := IsInteger("\U{0005}aa\U{0001}\U{0003}");
expect r0 <==> |"\U{0005}aa\U{0001}\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0005}aa\U{0001}\U{0003}"| ==> IsDigit("\U{0005}aa\U{0001}\U{0003}"[i]);
}
method {:test} Test15() {
var r0 := IsInteger("\U{0018}aa\0\U{0002}\U{0004}");
expect r0 <==> |"\U{0018}aa\0\U{0002}\U{0004}"| > 0 && forall i :: 0 <= i < |"\U{0018}aa\0\U{0002}\U{0004}"| ==> IsDigit("\U{0018}aa\0\U{0002}\U{0004}"[i]);
}

// REPEAT 8 - TIME: 11.4977665 s

method {:test} Test16() {
var r0 := IsInteger("\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}");
expect r0 <==> |"\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}"| > 0 && forall i :: 0 <= i < |"\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}"| ==> IsDigit("\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}"[i]);
}
method {:test} Test17() {
var r0 := IsInteger("\naaa\0\U{0001}aaaa\U{0002}");
expect r0 <==> |"\naaa\0\U{0001}aaaa\U{0002}"| > 0 && forall i :: 0 <= i < |"\naaa\0\U{0001}aaaa\U{0002}"| ==> IsDigit("\naaa\0\U{0001}aaaa\U{0002}"[i]);
}

// REPEAT 9 - TIME: 12.524172 s

method {:test} Test18() {
var r0 := IsInteger("\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}");
expect r0 <==> |"\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}"| > 0 && forall i :: 0 <= i < |"\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}"| ==> IsDigit("\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}"[i]);
}
method {:test} Test19() {
var r0 := IsInteger("aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}");
expect r0 <==> |"aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}"| > 0 && forall i :: 0 <= i < |"aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}"| ==> IsDigit("aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}"[i]);
}

// REPEAT 10 - TIME: 13.514132 s
