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

method {:test} Test11() {
var r0 := IsInteger("9a9a7a4");
expect r0 <==> |"9a9a7a4"| > 0 && forall i :: 0 <= i < |"9a9a7a4"| ==> IsDigit("9a9a7a4"[i]);
}
method {:test} Test12() {
var r0 := IsInteger("aaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaa\t"[i]);
}

// REPEAT 6 - TIME: 105.5319915 s
