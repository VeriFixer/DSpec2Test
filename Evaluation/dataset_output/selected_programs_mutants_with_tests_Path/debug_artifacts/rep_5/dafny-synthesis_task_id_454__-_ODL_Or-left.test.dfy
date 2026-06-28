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

method {:test} Test12() {
var r0 := ContainsZ("\U{0004}a\0aaaa\U{0002}a\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0aaaa\U{0002}a\U{0006}"| && ("\U{0004}a\0aaaa\U{0002}a\U{0006}"[i] == 'z' || "\U{0004}a\0aaaa\U{0002}a\U{0006}"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("Zaa\0aaaaa\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"Zaa\0aaaaa\U{0002}"| && ("Zaa\0aaaaa\U{0002}"[i] == 'z' || "Zaa\0aaaaa\U{0002}"[i] == 'Z');
}

// REPEAT 5 - TIME: 228.5444939 s
