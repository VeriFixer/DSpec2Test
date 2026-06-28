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

method {:test} Test9() {
var r0 := ContainsZ("\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}"| && ("\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}"[i] == 'z' || "\U{0002}aaaaaaaa\U{0004}aaa\0aaa\U{0006}"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("Zaaaaaaaa\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"Zaaaaaaaa\0\U{0002}"| && ("Zaaaaaaaa\0\U{0002}"[i] == 'z' || "Zaaaaaaaa\0\U{0002}"[i] == 'Z');
}

// REPEAT 4 - TIME: 164.8508316 s
