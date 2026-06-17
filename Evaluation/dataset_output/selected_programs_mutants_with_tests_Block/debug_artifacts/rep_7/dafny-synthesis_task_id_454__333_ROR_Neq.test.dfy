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

method {:test} Test12() {
var r0 := ContainsZ("\U{0004}a\0Za\U{0002}aaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0Za\U{0002}aaaaaa"| && ("\U{0004}a\0Za\U{0002}aaaaaa"[i] == 'z' || "\U{0004}a\0Za\U{0002}aaaaaa"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\0\U{0002}za\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}za\U{0004}"| && ("\0\U{0002}za\U{0004}"[i] == 'z' || "\0\U{0002}za\U{0004}"[i] == 'Z');
}

// REPEAT 7 - TIME: 11.4385002 s
