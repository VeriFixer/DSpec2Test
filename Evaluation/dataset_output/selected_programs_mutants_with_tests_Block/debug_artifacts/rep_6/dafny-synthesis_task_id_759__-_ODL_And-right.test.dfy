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

method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| && "\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"[i] == '.' && |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| && "\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"[i] == '.' && |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaa\0aa"| && "\U{0002}aaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaa\0aa"| && "\U{0002}aaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 9.7115901 s
