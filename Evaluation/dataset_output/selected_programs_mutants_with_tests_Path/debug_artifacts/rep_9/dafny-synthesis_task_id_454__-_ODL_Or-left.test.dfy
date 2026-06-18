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

method {:test} Test24() {
var r0 := ContainsZ("\U{000C}aaaaaaaaaa\0aaaaaa\U{0004}a\U{0006}\U{0002}\U{0008}a\n");
expect r0 <==> exists i :: 0 <= i < |"\U{000C}aaaaaaaaaa\0aaaaaa\U{0004}a\U{0006}\U{0002}\U{0008}a\n"| && ("\U{000C}aaaaaaaaaa\0aaaaaa\U{0004}a\U{0006}\U{0002}\U{0008}a\n"[i] == 'z' || "\U{000C}aaaaaaaaaa\0aaaaaa\U{0004}a\U{0006}\U{0002}\U{0008}a\n"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("aaaaaaaaaZaaaaa\U{0001}aaaaaaaaaaa\U{0003}a");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaZaaaaa\U{0001}aaaaaaaaaaa\U{0003}a"| && ("aaaaaaaaaZaaaaa\U{0001}aaaaaaaaaaa\U{0003}a"[i] == 'z' || "aaaaaaaaaZaaaaa\U{0001}aaaaaaaaaaa\U{0003}a"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaZa\U{0003}aaa\U{0001}aa\U{0005}a");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaZa\U{0003}aaa\U{0001}aa\U{0005}a"| && ("aaaaaaaaaaaaaaaaaaZa\U{0003}aaa\U{0001}aa\U{0005}a"[i] == 'z' || "aaaaaaaaaaaaaaaaaaZa\U{0003}aaa\U{0001}aa\U{0005}a"[i] == 'Z');
}

// REPEAT 9 - TIME: 657.2638847 s
