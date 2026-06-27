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

method {:test} Test17() {
var r0 := IsInteger("4aa474a7aaaaaaaa828aa");
expect r0 <==> |"4aa474a7aaaaaaaa828aa"| > 0 && forall i :: 0 <= i < |"4aa474a7aaaaaaaa828aa"| ==> IsDigit("4aa474a7aaaaaaaa828aa"[i]);
}
method {:test} Test18() {
var r0 := IsInteger("\U{0001}aa\U{0019}aa\0");
expect r0 <==> |"\U{0001}aa\U{0019}aa\0"| > 0 && forall i :: 0 <= i < |"\U{0001}aa\U{0019}aa\0"| ==> IsDigit("\U{0001}aa\U{0019}aa\0"[i]);
}

// REPEAT 9 - TIME: 18.5012359 s
