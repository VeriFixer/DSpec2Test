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

method {:test} Test2() {
var r0 := ContainsZ("aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}"| && ("aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}"[i] == 'z' || "aaaaaaaa\U{0001}aaaaaaaaaaaZ\U{0003}"[i] == 'Z');
}
method {:test} Test3() {
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}

// REPEAT 2 - TIME: 4.0356094 s
