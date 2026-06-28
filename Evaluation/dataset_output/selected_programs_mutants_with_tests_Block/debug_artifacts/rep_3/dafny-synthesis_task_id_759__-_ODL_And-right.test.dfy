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

method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\0.aa");
expect r0 ==> exists i :: 0 <= i < |"\0.aa"| && "\0.aa"[i] == '.' && |"\0.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0.aa"| && "\0.aa"[i] == '.' && |"\0.aa"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("a\U{0002}\U{0004}a\0");
expect r0 ==> exists i :: 0 <= i < |"a\U{0002}\U{0004}a\0"| && "a\U{0002}\U{0004}a\0"[i] == '.' && |"a\U{0002}\U{0004}a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\U{0002}\U{0004}a\0"| && "a\U{0002}\U{0004}a\0"[i] == '.' && |"a\U{0002}\U{0004}a\0"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 6.5731445 s
