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

method {:test} Test27() {
var r0 := ContainsZ("aa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}\U{0002}aaaa");
expect r0 <==> exists i :: 0 <= i < |"aa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}\U{0002}aaaa"| && ("aa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}\U{0002}aaaa"[i] == 'z' || "aa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}\U{0002}aaaa"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0001}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0001}"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\0");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\0"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\0"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\0"[i] == 'Z');
}

// REPEAT 10 - TIME: 756.9045389 s
