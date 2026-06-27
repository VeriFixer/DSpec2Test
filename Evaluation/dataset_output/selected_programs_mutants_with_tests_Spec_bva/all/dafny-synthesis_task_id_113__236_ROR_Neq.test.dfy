// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if |s| != 0 {
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
var r0 := IsInteger("");
expect r0 <==> |""| > 0 && forall i :: 0 <= i < |""| ==> IsDigit(""[i]);
}
method {:test} Test6() {
var r0 := IsInteger("a");
expect r0 <==> |"a"| > 0 && forall i :: 0 <= i < |"a"| ==> IsDigit("a"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("aa");
expect r0 <==> |"aa"| > 0 && forall i :: 0 <= i < |"aa"| ==> IsDigit("aa"[i]);
}
method {:test} Test13() {
var r0 := IsInteger("/");
expect r0 <==> |"/"| > 0 && forall i :: 0 <= i < |"/"| ==> IsDigit("/"[i]);
}
method {:test} Test15() {
var r0 := IsInteger("/a");
expect r0 <==> |"/a"| > 0 && forall i :: 0 <= i < |"/a"| ==> IsDigit("/a"[i]);
}

// REPEAT 1 - TIME: 13.6637284 s

method {:test} Test20() {
var r0 := IsInteger("a01");
expect r0 <==> |"a01"| > 0 && forall i :: 0 <= i < |"a01"| ==> IsDigit("a01"[i]);
}
method {:test} Test21() {
var r0 := IsInteger("\U{0001}\0\U{0008}");
expect r0 <==> |"\U{0001}\0\U{0008}"| > 0 && forall i :: 0 <= i < |"\U{0001}\0\U{0008}"| ==> IsDigit("\U{0001}\0\U{0008}"[i]);
}

// REPEAT 2 - TIME: 15.4651045 s

method {:test} Test22() {
var r0 := IsInteger("2aaaaa2aaaa4aa4");
expect r0 <==> |"2aaaaa2aaaa4aa4"| > 0 && forall i :: 0 <= i < |"2aaaaa2aaaa4aa4"| ==> IsDigit("2aaaaa2aaaa4aa4"[i]);
}
method {:test} Test23() {
var r0 := IsInteger("\0a\U{0008}a");
expect r0 <==> |"\0a\U{0008}a"| > 0 && forall i :: 0 <= i < |"\0a\U{0008}a"| ==> IsDigit("\0a\U{0008}a"[i]);
}

// REPEAT 3 - TIME: 17.2206176 s

method {:test} Test24() {
var r0 := IsInteger("7a49aaaaaa47a9a8");
expect r0 <==> |"7a49aaaaaa47a9a8"| > 0 && forall i :: 0 <= i < |"7a49aaaaaa47a9a8"| ==> IsDigit("7a49aaaaaa47a9a8"[i]);
}
method {:test} Test25() {
var r0 := IsInteger("\0a\U{0008}a");
expect r0 <==> |"\0a\U{0008}a"| > 0 && forall i :: 0 <= i < |"\0a\U{0008}a"| ==> IsDigit("\0a\U{0008}a"[i]);
}

// REPEAT 4 - TIME: 18.6942404 s

method {:test} Test26() {
var r0 := IsInteger("6a449");
expect r0 <==> |"6a449"| > 0 && forall i :: 0 <= i < |"6a449"| ==> IsDigit("6a449"[i]);
}
method {:test} Test27() {
var r0 := IsInteger("aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}");
expect r0 <==> |"aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}"| > 0 && forall i :: 0 <= i < |"aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}"| ==> IsDigit("aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}"[i]);
}

// REPEAT 5 - TIME: 20.066427 s

method {:test} Test28() {
var r0 := IsInteger("6424");
expect r0 <==> |"6424"| > 0 && forall i :: 0 <= i < |"6424"| ==> IsDigit("6424"[i]);
}
method {:test} Test29() {
var r0 := IsInteger("\U{0008}a");
expect r0 <==> |"\U{0008}a"| > 0 && forall i :: 0 <= i < |"\U{0008}a"| ==> IsDigit("\U{0008}a"[i]);
}

// REPEAT 6 - TIME: 21.369944 s

method {:test} Test30() {
var r0 := IsInteger("84a2a9");
expect r0 <==> |"84a2a9"| > 0 && forall i :: 0 <= i < |"84a2a9"| ==> IsDigit("84a2a9"[i]);
}
method {:test} Test31() {
var r0 := IsInteger("\U{0002}a\0\U{0018}\U{0001}");
expect r0 <==> |"\U{0002}a\0\U{0018}\U{0001}"| > 0 && forall i :: 0 <= i < |"\U{0002}a\0\U{0018}\U{0001}"| ==> IsDigit("\U{0002}a\0\U{0018}\U{0001}"[i]);
}

// REPEAT 7 - TIME: 22.7684191 s

method {:test} Test32() {
var r0 := IsInteger("7aaaa8a49aaa6aa298");
expect r0 <==> |"7aaaa8a49aaa6aa298"| > 0 && forall i :: 0 <= i < |"7aaaa8a49aaa6aa298"| ==> IsDigit("7aaaa8a49aaa6aa298"[i]);
}
method {:test} Test33() {
var r0 := IsInteger("\U{0002}a\U{0008}aaaa\U{0001}aaaa\0aa\U{0003}aa");
expect r0 <==> |"\U{0002}a\U{0008}aaaa\U{0001}aaaa\0aa\U{0003}aa"| > 0 && forall i :: 0 <= i < |"\U{0002}a\U{0008}aaaa\U{0001}aaaa\0aa\U{0003}aa"| ==> IsDigit("\U{0002}a\U{0008}aaaa\U{0001}aaaa\0aa\U{0003}aa"[i]);
}

// REPEAT 8 - TIME: 24.0802855 s

method {:test} Test34() {
var r0 := IsInteger("6aa2447");
expect r0 <==> |"6aa2447"| > 0 && forall i :: 0 <= i < |"6aa2447"| ==> IsDigit("6aa2447"[i]);
}
method {:test} Test35() {
var r0 := IsInteger("\U{0004}a\0\U{0008}\U{0001}\U{0002}\U{0003}");
expect r0 <==> |"\U{0004}a\0\U{0008}\U{0001}\U{0002}\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0004}a\0\U{0008}\U{0001}\U{0002}\U{0003}"| ==> IsDigit("\U{0004}a\0\U{0008}\U{0001}\U{0002}\U{0003}"[i]);
}

// REPEAT 9 - TIME: 25.8703017 s

method {:test} Test36() {
var r0 := IsInteger("aaaaa44aaa2a4aa9a27");
expect r0 <==> |"aaaaa44aaa2a4aa9a27"| > 0 && forall i :: 0 <= i < |"aaaaa44aaa2a4aa9a27"| ==> IsDigit("aaaaa44aaa2a4aa9a27"[i]);
}
method {:test} Test37() {
var r0 := IsInteger("\U{000B}aa\U{0002}aa\U{0007}aa\U{0004}a\0\U{0005}a\U{0003}\U{0001}\U{0008}\U{0006}\t");
expect r0 <==> |"\U{000B}aa\U{0002}aa\U{0007}aa\U{0004}a\0\U{0005}a\U{0003}\U{0001}\U{0008}\U{0006}\t"| > 0 && forall i :: 0 <= i < |"\U{000B}aa\U{0002}aa\U{0007}aa\U{0004}a\0\U{0005}a\U{0003}\U{0001}\U{0008}\U{0006}\t"| ==> IsDigit("\U{000B}aa\U{0002}aa\U{0007}aa\U{0004}a\0\U{0005}a\U{0003}\U{0001}\U{0008}\U{0006}\t"[i]);
}

// REPEAT 10 - TIME: 27.5902688 s
