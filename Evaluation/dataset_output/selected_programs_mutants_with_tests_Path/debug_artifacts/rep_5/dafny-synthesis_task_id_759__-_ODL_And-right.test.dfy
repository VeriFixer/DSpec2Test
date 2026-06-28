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

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}a\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}a\0\U{0002}"| && "\U{0004}a\0\U{0002}"[i] == '.' && |"\U{0004}a\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}a\0\U{0002}"| && "\U{0004}a\0\U{0002}"[i] == '.' && |"\U{0004}a\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa\0aa.\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| && "aaaaaaaaa\0aa.\U{0004}\U{0002}"[i] == '.' && |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| && "aaaaaaaaa\0aa.\U{0004}\U{0002}"[i] == '.' && |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\0aaaaaa.\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| && "aaaaa\0aaaaaa.\U{0004}\U{0002}"[i] == '.' && |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| && "aaaaa\0aaaaaa.\U{0004}\U{0002}"[i] == '.' && |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 151.2060275 s
