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

method {:test} Test16() {
var r0 := IsInteger("-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}");
expect r0 <==> |"-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}"| > 0 && forall i :: 0 <= i < |"-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}"| ==> IsDigit("-aaaaaaaaa\U{0004}\U{000E}aa\U{0010}a\U{0006}\U{0008}\U{000C}a\0a\na\U{0002}\U{0012}aa\U{0014}"[i]);
}
method {:test} Test17() {
var r0 := IsInteger("\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r");
expect r0 <==> |"\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r"| > 0 && forall i :: 0 <= i < |"\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r"| ==> IsDigit("\U{0012}aa\U{0001}\U{0007}aaaaaaaaaaaaaaaa\t\U{000B}\U{0003}aa\U{0005}a\r"[i]);
}

// REPEAT 9 - TIME: 12.8284846 s
