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

method {:test} Test18() {
var r0 := IsInteger("2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}");
expect r0 <==> |"2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}"| > 0 && forall i :: 0 <= i < |"2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}"| ==> IsDigit("2\U{000F}\U{0001}aaaaaaa\raaaa\U{0005}a\U{000F}a\U{0003}\U{000B}a\taaaa\U{0007}a\U{0011}"[i]);
}
method {:test} Test19() {
var r0 := IsInteger("\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}");
expect r0 <==> |"\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}"| > 0 && forall i :: 0 <= i < |"\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}"| ==> IsDigit("\naaaaaaaaaaaaaa\0aaaaaa\U{0001}aaaaaa\U{0002}"[i]);
}

// REPEAT 10 - TIME: 14.0078192 s
