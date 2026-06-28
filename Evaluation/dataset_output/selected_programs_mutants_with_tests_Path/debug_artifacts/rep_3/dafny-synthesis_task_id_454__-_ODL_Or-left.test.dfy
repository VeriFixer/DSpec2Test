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

method {:test} Test6() {
var r0 := ContainsZ("\0aa");
expect r0 <==> exists i :: 0 <= i < |"\0aa"| && ("\0aa"[i] == 'z' || "\0aa"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}"| && ("\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}"[i] == 'z' || "\U{0004}a\U{0002}\0aaaaaaaaaaaZ\U{0006}"[i] == 'Z');
}

// REPEAT 3 - TIME: 111.0073601 s
