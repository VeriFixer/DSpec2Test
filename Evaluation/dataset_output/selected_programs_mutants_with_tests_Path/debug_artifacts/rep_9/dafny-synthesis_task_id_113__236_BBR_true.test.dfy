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
var r0 := IsInteger("aaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test18() {
var r0 := IsInteger("aaaaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 9 - TIME: 191.6121132 s
