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
var r0 := IsDecimalWithTwoPrecision("aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| && "aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"[i] == '.' && |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| && "aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"[i] == '.' && |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0aa"| && "\U{0002}\0aa"[i] == '.' && |"\U{0002}\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0aa"| && "\U{0002}\0aa"[i] == '.' && |"\U{0002}\0aa"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 13.8997942 s
