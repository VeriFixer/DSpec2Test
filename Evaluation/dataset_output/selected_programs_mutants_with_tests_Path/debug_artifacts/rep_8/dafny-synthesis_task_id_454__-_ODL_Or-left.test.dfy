// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test21() {
var r0 := ContainsZ("\U{0004}a\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0\U{0002}"| && ("\U{0004}a\0\U{0002}"[i] == 'z' || "\U{0004}a\0\U{0002}"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}"| && ("aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}"[i] == 'z' || "aaaaaaaaaZa\0aaa\U{0004}aaa\U{0006}\naaaaaa\U{0002}a\U{0008}"[i] == 'Z');
}

// REPEAT 8 - TIME: 484.3537131 s
