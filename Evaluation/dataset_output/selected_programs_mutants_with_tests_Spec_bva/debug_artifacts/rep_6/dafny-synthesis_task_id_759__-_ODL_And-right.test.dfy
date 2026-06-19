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

method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaa\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| && "\0aaaaaaaaaaaa\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| && "\0aaaaaaaaaaaa\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}");
expect r0 ==> exists i :: 0 <= i < |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| && "\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"[i] == '.' && |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| && "\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"[i] == '.' && |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 15.2142367 s
