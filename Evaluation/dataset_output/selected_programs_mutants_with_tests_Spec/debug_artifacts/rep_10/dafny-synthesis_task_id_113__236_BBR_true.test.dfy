// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if true {
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

method {:test} Test19() {
var r0 := IsInteger("2aaaaaaaaaaaa7826aaa499aaa4");
expect r0 <==> |"2aaaaaaaaaaaa7826aaa499aaa4"| > 0 && forall i :: 0 <= i < |"2aaaaaaaaaaaa7826aaa499aaa4"| ==> IsDigit("2aaaaaaaaaaaa7826aaa499aaa4"[i]);
}
method {:test} Test20() {
var r0 := IsInteger("\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}");
expect r0 <==> |"\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}"| > 0 && forall i :: 0 <= i < |"\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}"| ==> IsDigit("\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}"[i]);
}

// REPEAT 10 - TIME: 21.1062192 s
