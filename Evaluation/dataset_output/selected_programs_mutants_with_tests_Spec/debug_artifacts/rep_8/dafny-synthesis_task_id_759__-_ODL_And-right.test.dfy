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

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}a\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}a\U{0004}\0"| && "\U{0002}a\U{0004}\0"[i] == '.' && |"\U{0002}a\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}a\U{0004}\0"| && "\U{0002}a\U{0004}\0"[i] == '.' && |"\U{0002}a\U{0004}\0"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\raaaaaaaa\U{0005}\U{0001}aaaa\U{0007}\taaaa.\U{0003}\U{000B}");
expect r0 ==> exists i :: 0 <= i < |"\raaaaaaaa\U{0005}\U{0001}aaaa\U{0007}\taaaa.\U{0003}\U{000B}"| && "\raaaaaaaa\U{0005}\U{0001}aaaa\U{0007}\taaaa.\U{0003}\U{000B}"[i] == '.' && |"\raaaaaaaa\U{0005}\U{0001}aaaa\U{0007}\taaaa.\U{0003}\U{000B}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\raaaaaaaa\U{0005}\U{0001}aaaa\U{0007}\taaaa.\U{0003}\U{000B}"| && "\raaaaaaaa\U{0005}\U{0001}aaaa\U{0007}\taaaa.\U{0003}\U{000B}"[i] == '.' && |"\raaaaaaaa\U{0005}\U{0001}aaaa\U{0007}\taaaa.\U{0003}\U{000B}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 13.3067464 s
