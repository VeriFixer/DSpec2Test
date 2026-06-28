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

// REPEAT 1 - TIME: 17.7723403 s

method {:test} Test20() {
var r0 := IsInteger("a02");
expect r0 <==> |"a02"| > 0 && forall i :: 0 <= i < |"a02"| ==> IsDigit("a02"[i]);
}
method {:test} Test21() {
var r0 := IsInteger("aa\U{0008}");
expect r0 <==> |"aa\U{0008}"| > 0 && forall i :: 0 <= i < |"aa\U{0008}"| ==> IsDigit("aa\U{0008}"[i]);
}

// REPEAT 2 - TIME: 19.5045258 s

method {:test} Test22() {
var r0 := IsInteger("81a");
expect r0 <==> |"81a"| > 0 && forall i :: 0 <= i < |"81a"| ==> IsDigit("81a"[i]);
}
method {:test} Test23() {
var r0 := IsInteger("a\U{0001}\n\0");
expect r0 <==> |"a\U{0001}\n\0"| > 0 && forall i :: 0 <= i < |"a\U{0001}\n\0"| ==> IsDigit("a\U{0001}\n\0"[i]);
}

// REPEAT 3 - TIME: 21.6051437 s

method {:test} Test24() {
var r0 := IsInteger("aa0a1");
expect r0 <==> |"aa0a1"| > 0 && forall i :: 0 <= i < |"aa0a1"| ==> IsDigit("aa0a1"[i]);
}
method {:test} Test25() {
var r0 := IsInteger("\U{0001}\0a%\U{0002}");
expect r0 <==> |"\U{0001}\0a%\U{0002}"| > 0 && forall i :: 0 <= i < |"\U{0001}\0a%\U{0002}"| ==> IsDigit("\U{0001}\0a%\U{0002}"[i]);
}

// REPEAT 4 - TIME: 23.5171113 s

method {:test} Test26() {
var r0 := IsInteger("7a2aa");
expect r0 <==> |"7a2aa"| > 0 && forall i :: 0 <= i < |"7a2aa"| ==> IsDigit("7a2aa"[i]);
}
method {:test} Test27() {
var r0 := IsInteger("\U{0002}a\U{0008}\0\U{0001}\U{0003}");
expect r0 <==> |"\U{0002}a\U{0008}\0\U{0001}\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0002}a\U{0008}\0\U{0001}\U{0003}"| ==> IsDigit("\U{0002}a\U{0008}\0\U{0001}\U{0003}"[i]);
}

// REPEAT 5 - TIME: 25.4018902 s

method {:test} Test28() {
var r0 := IsInteger("9a22a4");
expect r0 <==> |"9a22a4"| > 0 && forall i :: 0 <= i < |"9a22a4"| ==> IsDigit("9a22a4"[i]);
}
method {:test} Test29() {
var r0 := IsInteger("\U{0001}aa\U{0008}\0");
expect r0 <==> |"\U{0001}aa\U{0008}\0"| > 0 && forall i :: 0 <= i < |"\U{0001}aa\U{0008}\0"| ==> IsDigit("\U{0001}aa\U{0008}\0"[i]);
}

// REPEAT 6 - TIME: 27.2280154 s

method {:test} Test30() {
var r0 := IsInteger("2aa4a98");
expect r0 <==> |"2aa4a98"| > 0 && forall i :: 0 <= i < |"2aa4a98"| ==> IsDigit("2aa4a98"[i]);
}
method {:test} Test31() {
var r0 := IsInteger("\U{0002}\0\U{0008}\U{0001}");
expect r0 <==> |"\U{0002}\0\U{0008}\U{0001}"| > 0 && forall i :: 0 <= i < |"\U{0002}\0\U{0008}\U{0001}"| ==> IsDigit("\U{0002}\0\U{0008}\U{0001}"[i]);
}

// REPEAT 7 - TIME: 29.288896 s

method {:test} Test32() {
var r0 := IsInteger("2aa49a96");
expect r0 <==> |"2aa49a96"| > 0 && forall i :: 0 <= i < |"2aa49a96"| ==> IsDigit("2aa49a96"[i]);
}
method {:test} Test33() {
var r0 := IsInteger("\0aaa\U{0001}\U{0002}\U{0018}\U{0003}");
expect r0 <==> |"\0aaa\U{0001}\U{0002}\U{0018}\U{0003}"| > 0 && forall i :: 0 <= i < |"\0aaa\U{0001}\U{0002}\U{0018}\U{0003}"| ==> IsDigit("\0aaa\U{0001}\U{0002}\U{0018}\U{0003}"[i]);
}

// REPEAT 8 - TIME: 31.5122615 s

method {:test} Test34() {
var r0 := IsInteger("4798824982aaa1");
expect r0 <==> |"4798824982aaa1"| > 0 && forall i :: 0 <= i < |"4798824982aaa1"| ==> IsDigit("4798824982aaa1"[i]);
}
method {:test} Test35() {
var r0 := IsInteger("\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a");
expect r0 <==> |"\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a"| > 0 && forall i :: 0 <= i < |"\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a"| ==> IsDigit("\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a"[i]);
}

// REPEAT 9 - TIME: 33.5541379 s

method {:test} Test36() {
var r0 := IsInteger("7a4aaa6978");
expect r0 <==> |"7a4aaa6978"| > 0 && forall i :: 0 <= i < |"7a4aaa6978"| ==> IsDigit("7a4aaa6978"[i]);
}
method {:test} Test37() {
var r0 := IsInteger("aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}");
expect r0 <==> |"aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}"| > 0 && forall i :: 0 <= i < |"aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}"| ==> IsDigit("aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}"[i]);
}

// REPEAT 10 - TIME: 35.3232692 s
