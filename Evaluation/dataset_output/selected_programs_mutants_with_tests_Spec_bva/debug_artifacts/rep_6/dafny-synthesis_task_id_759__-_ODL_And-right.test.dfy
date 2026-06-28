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
var r0 := IsDecimalWithTwoPrecision("\U{0004}aa\U{0002}\U{0008}a\U{0006}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| && "\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"[i] == '.' && |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| && "\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"[i] == '.' && |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}aa\U{0001}aaaaa.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| && "\U{0005}aa\U{0001}aaaaa.\U{0003}a"[i] == '.' && |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| && "\U{0005}aa\U{0001}aaaaa.\U{0003}a"[i] == '.' && |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 21.1223855 s
