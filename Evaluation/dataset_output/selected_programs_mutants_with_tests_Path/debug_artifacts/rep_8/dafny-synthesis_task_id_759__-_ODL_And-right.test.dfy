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

method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}\U{0004}a\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}\U{0004}a\U{0002}\0"| && "\U{0006}\U{0004}a\U{0002}\0"[i] == '.' && |"\U{0006}\U{0004}a\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}\U{0004}a\U{0002}\0"| && "\U{0006}\U{0004}a\U{0002}\0"[i] == '.' && |"\U{0006}\U{0004}a\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| && "aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| && "aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaa\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 357.9902958 s
