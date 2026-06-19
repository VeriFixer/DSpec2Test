// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' <== s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test3() {
var r0 := ContainsZ("aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}"| && ("aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}"[i] == 'z' || "aaaaaaaaz\U{0003}aaaaaaaaaaa\U{0001}"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("\0");
expect r0 <==> exists i :: 0 <= i < |"\0"| && ("\0"[i] == 'z' || "\0"[i] == 'Z');
}

// REPEAT 2 - TIME: 5.0668901 s
