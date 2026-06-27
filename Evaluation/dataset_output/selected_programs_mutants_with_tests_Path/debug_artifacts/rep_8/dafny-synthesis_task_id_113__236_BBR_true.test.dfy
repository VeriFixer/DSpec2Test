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

method {:test} Test15() {
var r0 := IsInteger("aaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test16() {
var r0 := IsInteger("aaaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 8 - TIME: 162.780375 s
