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
var r0 := ContainsZ("\U{000C}aaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}\0aaaa\U{0008}\n");
expect r0 <==> exists i :: 0 <= i < |"\U{000C}aaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}\0aaaa\U{0008}\n"| && ("\U{000C}aaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}\0aaaa\U{0008}\n"[i] == 'z' || "\U{000C}aaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}\0aaaa\U{0008}\n"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaZaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaZaaaaaaaa"| && ("aaaaaaaaaaaaaaaaaaaZaaaaaaaa"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaZaaaaaaaa"[i] == 'Z');
}

// REPEAT 8 - TIME: 557.8271066 s
