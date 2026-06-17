// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] != 'z' || s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test16() {
var r0 := ContainsZ("Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"| && ("Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"[i] == 'z' || "Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"| && ("\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"[i] == 'z' || "\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 13.6269847 s
