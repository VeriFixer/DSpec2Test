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
var r0 := ContainsZ("\U{0002}a\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0"| && ("\U{0002}a\0"[i] == 'z' || "\U{0002}a\0"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("aaZaaaaaaa\0aaaaaaaaa\U{0002}a\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"aaZaaaaaaa\0aaaaaaaaa\U{0002}a\U{0004}"| && ("aaZaaaaaaa\0aaaaaaaaa\U{0002}a\U{0004}"[i] == 'z' || "aaZaaaaaaa\0aaaaaaaaa\U{0002}a\U{0004}"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("Za\0aaaaaaaaaaaaaaa\U{0002}a\U{0004}a\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"Za\0aaaaaaaaaaaaaaa\U{0002}a\U{0004}a\U{0006}"| && ("Za\0aaaaaaaaaaaaaaa\U{0002}a\U{0004}a\U{0006}"[i] == 'z' || "Za\0aaaaaaaaaaaaaaa\U{0002}a\U{0004}a\U{0006}"[i] == 'Z');
}

// REPEAT 3 - TIME: 126.4468097 s
