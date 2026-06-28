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

method {:test} Test4() {
var r0 := IsInteger("\t0");
expect r0 <==> |"\t0"| > 0 && forall i :: 0 <= i < |"\t0"| ==> IsDigit("\t0"[i]);
}
method {:test} Test5() {
var r0 := IsInteger("\taaaaaa\0");
expect r0 <==> |"\taaaaaa\0"| > 0 && forall i :: 0 <= i < |"\taaaaaa\0"| ==> IsDigit("\taaaaaa\0"[i]);
}

// REPEAT 3 - TIME: 5.1839332 s
