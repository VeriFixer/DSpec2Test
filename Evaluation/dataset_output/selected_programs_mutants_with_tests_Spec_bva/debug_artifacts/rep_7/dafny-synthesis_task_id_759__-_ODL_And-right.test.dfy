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

method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("\0a");
expect r0 ==> exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| && "\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"[i] == '.' && |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| && "\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"[i] == '.' && |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 16.0324809 s
