// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if |s| >= 0 {
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

method {:test} Test13() {
var r0 := IsInteger("2aaaa6aaa97a748");
expect r0 <==> |"2aaaa6aaa97a748"| > 0 && forall i :: 0 <= i < |"2aaaa6aaa97a748"| ==> IsDigit("2aaaa6aaa97a748"[i]);
}
method {:test} Test14() {
var r0 := IsInteger("\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa");
expect r0 <==> |"\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa"| > 0 && forall i :: 0 <= i < |"\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa"| ==> IsDigit("\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa"[i]);
}

// REPEAT 7 - TIME: 15.7531055 s
