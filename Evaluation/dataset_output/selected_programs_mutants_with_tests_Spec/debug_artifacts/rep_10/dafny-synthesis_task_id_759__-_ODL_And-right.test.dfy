// dafny-synthesis_task_id_759.dfy

method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  ensures result ==> exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  ensures !result ==> !exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
  {
    if s[i] == '.' {
      result := true;
      break;
    }
  }
}

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\U{0004}aaaa\U{000C}a\0aa\naa\U{0008}\U{0002}aa\U{000E}\U{0006}\U{0010}\U{0012}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\U{0004}aaaa\U{000C}a\0aa\naa\U{0008}\U{0002}aa\U{000E}\U{0006}\U{0010}\U{0012}"| && "aaaaa\U{0004}aaaa\U{000C}a\0aa\naa\U{0008}\U{0002}aa\U{000E}\U{0006}\U{0010}\U{0012}"[i] == '.' && |"aaaaa\U{0004}aaaa\U{000C}a\0aa\naa\U{0008}\U{0002}aa\U{000E}\U{0006}\U{0010}\U{0012}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\U{0004}aaaa\U{000C}a\0aa\naa\U{0008}\U{0002}aa\U{000E}\U{0006}\U{0010}\U{0012}"| && "aaaaa\U{0004}aaaa\U{000C}a\0aa\naa\U{0008}\U{0002}aa\U{000E}\U{0006}\U{0010}\U{0012}"[i] == '.' && |"aaaaa\U{0004}aaaa\U{000C}a\0aa\naa\U{0008}\U{0002}aa\U{000E}\U{0006}\U{0010}\U{0012}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}a\U{0001}.a\U{0003}");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}a\U{0001}.a\U{0003}"| && "\U{0005}a\U{0001}.a\U{0003}"[i] == '.' && |"\U{0005}a\U{0001}.a\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}a\U{0001}.a\U{0003}"| && "\U{0005}a\U{0001}.a\U{0003}"[i] == '.' && |"\U{0005}a\U{0001}.a\U{0003}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 15.8728067 s
