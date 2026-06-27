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

method {:test} Test19() {
var r0 := IsInteger("aaaaaaa1aaaaaa01aa");
expect r0 <==> |"aaaaaaa1aaaaaa01aa"| > 0 && forall i :: 0 <= i < |"aaaaaaa1aaaaaa01aa"| ==> IsDigit("aaaaaaa1aaaaaa01aa"[i]);
}
method {:test} Test20() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 10 - TIME: 216.7199755 s
